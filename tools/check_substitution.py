"""Required lifting/substitution proofs, independent replay, and actual Goose calls."""
from __future__ import annotations

from copy import deepcopy
import gzip
import hashlib
import io
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
from typing import Callable

import runtime
import substitution_harness as harness
import substitution_profile as profile
from check_expression_dag import compressed_input, exact
from check_stored_bindings import itf_value

LEAN_SOURCES = {"formal/lean/Substitution.lean", "formal/lean/SubstitutionAudit.lean",
                "formal/lean/SubstitutionReplay.lean"}
QUINT_SOURCES = {"formal/quint/Substitution.qnt"}
IMPLEMENTATIONS = {"tools/check_substitution.py", "tools/substitution_profile.py",
                   "tools/substitution_harness.py", "reference/substitution-driver.goose",
                   "formal/quint/substitution_replay.py"}
DOCUMENTS = {"docs/substitution.md", "schemas/substitution-replay-v1.md"}
LEAN_OBLIGATIONS = {"GooseSubstitution." + name for name in (
    "lift_var_below", "lift_var_at_or_above", "lift_lambda", "lift_pi", "lift_let",
    "lift_zero", "lift_add", "lift_preserves_height", "lift_fixed_of_scoped", "lift_closed",
    "lift_scope", "lift_loose_bound", "substitute_var_below", "substitute_var_equal",
    "substitute_var_above", "substitute_lambda", "substitute_pi", "substitute_let",
    "substitute_fixed_of_scoped", "substitute_closed", "substitute_scope", "substitute_closed_top",
    "substitute_lift_one", "substitute_lift_one_top", "substitute_variable_after_lift",
    "lambda_substitution_avoids_capture", "pi_substitution_avoids_capture",
    "let_substitution_avoids_capture", "nested_lambda_substitution_avoids_capture",
    "nested_lambda_free_variable_stays_free", "refused_observation_is_empty", "observe_has_no_authority",
)}
QUINT_TESTS = {
    "liftZeroTest", "liftBelowCutoffTest", "liftAtCutoffTest", "liftAboveCutoffTest",
    "sortPayloadUnchangedTest", "constantNameUnchangedTest", "applicationBothChildrenTest",
    "lambdaDomainAndBodyTest", "piDomainAndBodyTest", "letValueAndBodyTest",
    "substituteBelowCutoffTest", "substituteAtCutoffTest", "substituteAboveCutoffTest",
    "substituteApplicationTest", "lambdaAvoidsCaptureTest", "piAvoidsCaptureTest", "letAvoidsCaptureTest",
    "nestedBindersAvoidCaptureTest", "replacementOwnBinderTest", "sharedNodeDifferentDepthsTest",
    "selectedRootNotLastTest", "hugeCutoffDoesNotBoundTraversalTest", "closedSubstitutionResultTest",
    "emptyDepthQueriesTest", "selfReferenceRefusalTest", "forwardReferenceRefusalTest",
    "unusedInvalidSuffixRefusalTest", "authorityPreservedTest", "triangularRowsCoverAllContextsTest",
    "simulationBoundStuttersTest",
}
QUINT_OBLIGATIONS = {"Substitution." + name for name in QUINT_TESTS | {"safety"}}
QUINT_REPLAY_CHUNK_SIZE = 128
MALFORMED_REQUEST_COUNT = 22
NATIVE_CONTROL_COUNT = 14
ORDINARY_CONTROL_COUNT = 8
NATIVE_COMMAND_COUNT = profile.CASE_COUNT + NATIVE_CONTROL_COUNT + 2 * ORDINARY_CONTROL_COUNT


def counterexample(exit_code: int, text: str, path: Path) -> None:
    if type(exit_code) is not int or exit_code != 1 or "[violation] Found an issue" not in text \
            or "error: Invariant violated" not in text:
        raise ValueError("unlifted replacement did not produce the designated invariant failure")
    witness = itf_value(profile.dag._json_object(path.read_text()))
    if set(witness) != {"#meta", "vars", "states"} or witness["vars"] != ["q", "observed"] \
            or not isinstance(witness["#meta"], dict) \
            or any(witness["#meta"].get(key) != value for key, value in
                   (("format", "ITF"), ("source", "Substitution.qnt"), ("status", "violation"))):
        raise ValueError("capture counterexample has an unexpected ITF source, status or variable inventory")
    states = witness.get("states", []) if isinstance(witness, dict) else []
    if not isinstance(states, list) or len(states) != 2 or any(not isinstance(state, dict) for state in states):
        raise ValueError("unlifted replacement did not produce its two-state witness")
    if any(set(state) != {"#meta", "q", "observed"} or not exact(state["#meta"], {"index": index})
           for index, state in enumerate(states)):
        raise ValueError("capture counterexample has missing, extra or reordered state fields")
    query = {"nodes": [
        {"tag": 0, "a": 0, "b": 0, "c": 0, "name": []},
        {"tag": 1, "a": 0, "b": 0, "c": 0, "name": []},
        {"tag": 1, "a": 1, "b": 0, "c": 0, "name": []},
        {"tag": 4, "a": 0, "b": 2, "c": 0, "name": []}],
        "operation": 1, "root": 3, "parameter": 1, "cutoff": 0}
    before = {"decoded": True, "acceptance_authority": False,
              "rows": [{"expression": [4, 0, 0, 1, 1], "height": 2, "loose": 1}]}
    after = {"decoded": True, "acceptance_authority": False,
             "rows": [{"expression": [4, 0, 0, 1, 0], "height": 2, "loose": 0}]}
    if not exact(states[0].get("q"), query) or not exact(states[1].get("q"), query) \
            or not exact(states[0].get("observed"), before) or not exact(states[1].get("observed"), after):
        raise ValueError("counterexample differs from capture of the free replacement beneath one lambda")


def replay(*, inventory: list[dict], output: Path, receipt: dict, lean_build: Path,
           lean: Path, lean_flags: list[str], env: dict, run: Callable) -> tuple[list[dict], dict]:
    inputs = "\n".join(profile.encode(case) for case in inventory) + "\n"
    record = compressed_input(output / "substitution-inputs.jsonl.gz", inputs)
    lean_results = profile.decode_models(run(
        [str(lean), *lean_flags, "--run", "SubstitutionReplay.lean"], lean_build, output, receipt,
        "substitution-lean-replay", env=env, stdin=inputs, compress_log=True), inventory)
    chunks = []
    for chunk_index, start in enumerate(range(0, len(inventory), QUINT_REPLAY_CHUNK_SIZE)):
        chunk = inventory[start:start + QUINT_REPLAY_CHUNK_SIZE]
        chunk_inputs = "\n".join(profile.encode(case) for case in chunk) + "\n"
        name = f"substitution-quint-replay-{chunk_index:03d}"
        quint_results = profile.decode_models(run(
            [sys.executable, str(runtime.ROOT / "formal/quint/substitution_replay.py")], runtime.ROOT,
            output, receipt, name, env=env, stdin=chunk_inputs, compress_log=True), chunk)
        if not exact(lean_results[start:start + len(chunk)], quint_results):
            raise ValueError(f"Lean and Quint disagree on transformed expressions, height, loose or scope at case {start}")
        chunks.append({"first_case_index": start, "case_count": len(chunk), "command_name": name,
                       "stdin_sha256": hashlib.sha256(chunk_inputs.encode()).hexdigest()})
    if sum(chunk["case_count"] for chunk in chunks) != len(inventory):
        raise ValueError("Quint chunks do not cover the complete ordered substitution inventory")
    record.update(quint_replay_chunk_size=QUINT_REPLAY_CHUNK_SIZE, quint_replay_chunks=chunks)
    return lean_results, record


def malformed_requests() -> list[tuple[str, str]]:
    """Authored framing failures; none is a mathematical topology refusal."""
    seed = {"nodes": [[1, 0, 0, 0, []]], "operation": 0, "root": 0,
            "parameter": 1, "cutoff": 0, "depths": [0, 1]}
    result = [("empty-stream", ""), ("blank-line", "\n"), ("broken-json", "{\n")]

    def add(name: str, change: Callable) -> None:
        value = deepcopy(seed)
        change(value)
        result.append((name, json.dumps(value, separators=(",", ":")) + "\n"))

    add("unknown-key", lambda q: q.update(extra=0))
    add("missing-key", lambda q: q.pop("cutoff"))
    add("empty-nodes", lambda q: q.update(nodes=[]))
    add("unknown-operation", lambda q: q.update(operation=2))
    add("boolean-operation", lambda q: q.update(operation=True))
    add("float-cutoff", lambda q: q.update(cutoff=0.0))
    add("negative-cutoff", lambda q: q.update(cutoff=-1))
    add("root-outside", lambda q: q.update(root=1))
    add("replacement-outside", lambda q: q.update(operation=1, parameter=1))
    add("boolean-depth", lambda q: q.update(depths=[True]))
    add("unknown-tag", lambda q: q["nodes"][0].__setitem__(0, 7))
    add("boolean-payload", lambda q: q["nodes"][0].__setitem__(1, True))
    add("nonzero-unused-field", lambda q: q["nodes"][0].__setitem__(2, 1))
    add("unexpected-name", lambda q: q["nodes"][0].__setitem__(4, [97]))
    add("empty-constant-name", lambda q: q.update(nodes=[[2, 0, 0, 0, []]]))
    add("invalid-constant-name", lambda q: q.update(nodes=[[2, 0, 0, 0, [32]]]))
    encoded = json.dumps(seed, separators=(",", ":"))
    result.append(("duplicate-key", encoded[:-1] + ',"cutoff":0}\n'))
    result.append(("nonfinite-number", encoded.replace('"cutoff":0', '"cutoff":NaN') + "\n"))
    result.append(("exponent-number", encoded.replace('"cutoff":0', '"cutoff":0e0') + "\n"))
    return result


def contract_controls(*, output: Path, receipt: dict, lean_build: Path, lean: Path,
                      lean_flags: list[str], env: dict, run: Callable) -> dict:
    commands = {
        "lean": ([str(lean), *lean_flags, "--run", "SubstitutionReplay.lean"], lean_build, 2,
                 "invalid substitution replay input:"),
        "quint": ([sys.executable, str(runtime.ROOT / "formal/quint/substitution_replay.py")], runtime.ROOT, 1,
                  "Quint substitution replay failed:"),
    }
    controls = malformed_requests()
    if len(controls) != MALFORMED_REQUEST_COUNT or len({name for name, _ in controls}) != MALFORMED_REQUEST_COUNT:
        raise ValueError("substitution malformed-request inventory changed")
    inputs = "\n".join(json.dumps({"id": name, "stdin": text}, separators=(",", ":"))
                       for name, text in controls) + "\n"
    input_record = compressed_input(output / "substitution-malformed-inputs.jsonl.gz", inputs)
    executed = []
    for name, stdin in controls:
        for engine, (command, cwd, expected_exit, diagnostic) in commands.items():
            label = f"substitution-{engine}-reject-{name}"
            stdout = run(command, cwd, output, receipt, label, env=env, stdin=stdin, expected_exit=expected_exit)
            if stdout != "" or not (output / f"{label}.log").read_text().startswith(diagnostic):
                raise ValueError(f"{engine} malformed-input control {name} did not fail closed with its own diagnostic")
            executed.append({"id": name, "engine": engine, "command_name": label, "exit_code": expected_exit})
    # The general replay accepts depth order/multiplicity and cutoffs larger than
    # the native CLI's numeric bound. These fixed answers exercise that contract.
    seed = {"nodes": [[1, 0, 0, 0, []]], "operation": 0, "root": 0, "parameter": 1,
            "cutoff": 0, "depths": []}
    requests, expected = [], []
    for depths, cutoff, wire, loose in (([], 0, [1, 1], 2), ([2, 0, 2, 1], 0, [1, 1], 2),
                                       ([0, 1, 1000000000], 1000000000, [1, 0], 1)):
        request = dict(seed, depths=depths, cutoff=cutoff)
        requests.append(request)
        expected.append({"decoded": True, "expressions": [wire], "heights": [1], "loose": [loose],
                         "scoped": [[loose <= depth for depth in depths]], "acceptance_authority": False})
    stdin = "\n".join(json.dumps(q, separators=(",", ":")) for q in requests) + "\n"
    positive_input = compressed_input(output / "substitution-contract-inputs.jsonl.gz", stdin)
    for engine, (command, cwd, _, _) in commands.items():
        stdout = run(command, cwd, output, receipt, f"substitution-{engine}-contract", env=env, stdin=stdin)
        rows = [profile.dag._json_object(line) for line in stdout.splitlines()]
        if not stdout.endswith("\n") or not exact(rows, expected):
            raise ValueError(f"{engine} changed general depth-list or large-cutoff replay behavior")
    return {"status": "passed", "malformed_cases": len(controls), "refusal_executions": len(executed),
            "positive_cases": len(requests), "positive_executions": 2, "inputs": input_record,
            "positive_inputs": positive_input, "refusals": executed}


def native_result(command: list[str]) -> dict:
    try:
        result = subprocess.run(command, cwd=runtime.ROOT, capture_output=True, text=True, timeout=15)
        return {"exit_code": result.returncode, "stdout": result.stdout, "stderr": result.stderr}
    except (OSError, subprocess.TimeoutExpired) as error:
        def output(value: object) -> str:
            return value.decode(errors="replace") if isinstance(value, bytes) else value if isinstance(value, str) else ""
        return {"exit_code": None, "stdout": output(getattr(error, "stdout", None)),
                "stderr": output(getattr(error, "stderr", None)), "execution_error": f"{type(error).__name__}: {error}"}


def execute(*, output: Path, receipt: dict, build: Path, lean_build: Path, lean: Path,
            lean_flags: list[str], quint: Path, goose: Path, gcc: Path, binary: Path,
            env: dict, seed: str, run: Callable) -> None:
    lane = {"status": "running", "scope": "capture-avoiding lifting and substitution; finite actual-function correspondence",
            "acceptance_authority": False}
    receipt["substitution"] = lane
    inventory = profile.cases()
    if len(inventory) != profile.CASE_COUNT or len({case["id"] for case in inventory}) != profile.CASE_COUNT:
        raise ValueError("substitution inventory differs from its declared finite bound")
    model = lean_build / "Substitution.olean"
    run([str(lean), *lean_flags, "-o", str(model), "Substitution.lean"], lean_build, output, receipt,
        "substitution-lean-build", env=env)
    audit = run([str(lean), *lean_flags, "SubstitutionAudit.lean"], lean_build, output, receipt,
                "substitution-lean-axiom-audit", env=env)
    match = re.search(r"Substitution axiom audit passed: (\d+) required theorems without axioms; "
                      r"(\d+) declarations; (\d+) theorem declarations; support axioms: \[propext\]", audit)
    if match is None or int(match[1]) != len(LEAN_OBLIGATIONS):
        raise ValueError("substitution audit did not confirm its entire required theorem inventory")
    lane["lean"] = {"status": "passed", "obligations": sorted(LEAN_OBLIGATIONS), "required_theorem_axioms": [],
                    "namespace_support_axiom_allowlist": ["propext"], "namespace_declarations": int(match[2]),
                    "namespace_theorem_declarations": int(match[3]), "compiled_model_sha256": runtime.sha256(model)}
    quint_root = runtime.ROOT / "formal/quint"
    run([str(quint), "typecheck", "Substitution.qnt"], quint_root, output, receipt, "substitution-quint-typecheck")
    tests = run([str(quint), "test", "Substitution.qnt", "--backend=typescript", "--max-samples=1", f"--seed={seed}"],
                quint_root, output, receipt, "substitution-quint-tests")
    if "30 passing" not in tests or any(f"ok {name} passed 1 test(s)" not in tests for name in QUINT_TESTS):
        raise ValueError("Quint did not execute the complete substitution deterministic test inventory")
    simulation = run([str(quint), "run", "Substitution.qnt", "--backend=typescript", "--invariant=safety",
        "--max-samples=1000", "--max-steps=8", f"--seed={seed}", "--verbosity=1"], quint_root,
        output, receipt, "substitution-quint-bounded-run")
    if "[ok] No violation found" not in simulation:
        raise ValueError("Quint did not complete the bounded substitution invariant check")
    trace = output / "substitution-quint-negative.itf.json"
    trace.unlink(missing_ok=True)
    run([str(quint), "run", "Substitution.qnt", "--backend=typescript", "--init=unsafeInit", "--step=unsafeStep",
        "--invariant=safety", "--max-samples=1", "--max-steps=1", f"--seed={seed}", "--verbosity=2",
        "--out-itf", str(trace)], quint_root, output, receipt, "substitution-quint-negative-control", expected_exit=1)
    counterexample(1, (output / "substitution-quint-negative-control.log").read_text(), trace)
    lane["quint"] = {"status": "passed", "tests": sorted(QUINT_TESTS), "backend": "typescript",
        "invariant": "Substitution.safety", "seed": seed, "max_samples": 1000, "max_steps": 8,
        "arena_node_bound": 6, "at_bound": "stutter", "payload_amount_cutoff_range": [0, 3],
        "unbounded_proof": False, "negative_control": {"witnessed": True, "expected_exit_code": 1,
            "mutation": "insert unlifted Var 0 beneath one lambda, capturing a free variable and changing loose from 1 to 0",
            "trace": trace.name, "sha256": runtime.sha256(trace)}}
    lane["replay_contract"] = contract_controls(output=output, receipt=receipt, lean_build=lean_build,
        lean=lean, lean_flags=lean_flags, env=env, run=run)
    predictions, inputs_record = replay(inventory=inventory, output=output, receipt=receipt, lean_build=lean_build,
        lean=lean, lean_flags=lean_flags, env=env, run=run)
    source, generated, native = build / "substitution.goose", build / "substitution.c", build / "substitution"
    provenance = harness.generate(runtime.ROOT, source)
    saved_source = output / "substitution-harness.goose"
    shutil.copyfile(source, saved_source)
    run([str(goose), *runtime.GOOSE_FLAGS, "-o", str(generated), str(source)], runtime.ROOT,
        output, receipt, "substitution-goose-emit")
    if "#define GS_DEBUG 1" not in generated.read_text():
        raise ValueError("generated substitution harness runtime checks are disabled")
    run([str(gcc), "-O2", str(generated), "-o", str(native), "-lm", "-pthread"], runtime.ROOT,
        output, receipt, "substitution-goose-build")
    harness.verify_generated((runtime.ROOT / harness.CHECKER).read_bytes(),
                             (runtime.ROOT / harness.DRIVER).read_bytes(), source.read_bytes())
    provenance.update(generated_source=saved_source.name, generated_c_sha256=runtime.sha256(generated),
                      binary_sha256=runtime.sha256(native), runtime_checks_enabled=True)
    lane["native_build"] = provenance
    controls, ordinary = profile.native_controls(), profile.ordinary_controls()
    if len(controls) != NATIVE_CONTROL_COUNT or len({c["id"] for c in controls}) != NATIVE_CONTROL_COUNT \
            or len(ordinary) != ORDINARY_CONTROL_COUNT or len({c["id"] for c in ordinary}) != ORDINARY_CONTROL_COUNT:
        raise ValueError("native substitution control inventory changed")
    fixture = build / "substitution.tsv"
    comparison = output / "substitution-native-comparison.jsonl.gz"
    native_commands, transformed, topology_refusals, node_payloads = 0, 0, 0, 0
    with comparison.open("wb") as raw, gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as zipped, \
            io.TextIOWrapper(zipped, encoding="utf-8", newline="\n") as log:
        def execute_native(identifier: str, text: str, args: list[str], executable: Path,
                           metadata: dict) -> dict:
            nonlocal native_commands
            fixture.write_text(text)
            command = [str(executable), args[0], str(fixture), *args[1:]]
            observed = native_result(command)
            log.write(json.dumps({"id": identifier, **metadata, "fixture": text,
                "fixture_sha256": runtime.sha256(fixture), "command": command, "timeout_seconds": 15,
                "native": observed}, separators=(",", ":")) + "\n")
            log.flush()
            native_commands += 1
            if observed.get("execution_error"):
                raise RuntimeError(observed["execution_error"])
            return observed

        for case, prediction in zip(inventory, predictions):
            result = execute_native(case["id"], profile.native_fixture(case), profile.native_arguments(case), native,
                                    {"kind": "model_comparison", "case": case, "model": prediction})
            observation = profile.check_native(case, prediction, **result)
            transformed += observation["status"] == "transformed"
            topology_refusals += observation["status"] == "parser_refused"
            node_payloads += observation.get("node_payloads", 0)
        for control in controls:
            result = execute_native(control["id"], control["fixture"], control["args"], native,
                                    {"kind": "native_control", "control": control})
            profile.check_control(control, **result)
        for control in ordinary:
            for mode in ("--trace", "--check"):
                result = execute_native(control["id"], control["fixture"], [mode], binary,
                                        {"kind": "ordinary_control", "mode": mode, "control": control})
                profile.check_ordinary(control, mode, **result)
    if native_commands != NATIVE_COMMAND_COUNT or transformed != profile.CASE_COUNT - profile.MALFORMED_CASE_COUNT \
            or topology_refusals != profile.MALFORMED_CASE_COUNT:
        raise ValueError("native substitution command or transformation inventory is incomplete")
    lane["finite_correspondence"] = {"status": "passed", "model_cases": len(inventory),
        "finite_graphs": profile.FINITE_GRAPH_COUNT, "graph_node_lengths": [1, 2], "finite_operations": profile.FINITE_CASE_COUNT,
        "lift_amounts": [0, 1, 2], "cutoffs": [0, 1, 2],
        "leaves": ["Sort 0", "Sort 1", "Var 0", "Var 1", "Var 2", "Var 3", "Const missing"],
        "named_cases": profile.NAMED_CASE_COUNT, "topology_refusals": topology_refusals, "depths": list(profile.DEPTHS),
        "transformed_results": transformed, "native_node_payloads": node_payloads,
        "native_controls": [{"id": c["id"], "category": c["category"], "exit_code": c["exit_code"],
                             "diagnostic_snapshot": c["envelope"]} for c in controls],
        "ordinary_controls": [{"id": c["id"], "outcomes": c["outcomes"], "modes": ["--trace", "--check"]} for c in ordinary],
        "native_process_executions": native_commands, "lean_quint_full_model_agreement": True,
        "native_projection": "actual lift/substitute result ID and full expression wire; every original raw node/ID preserved",
        "native_internal_free_or_height_observed": False, "universal_implementation_refinement": False,
        "inputs": inputs_record, "native_log": comparison.name, "native_log_sha256": runtime.sha256(comparison),
        "log_encoding": "gzip", "bounds": {"native_arena_nodes": profile.MAX_ARENA_NODES,
            "structural_wire_tokens_per_request": profile.MAX_WIRE_TOKENS, "model_line_bytes": profile.MAX_MODEL_LINE_BYTES}}
    lane["status"] = "passed"
    print(f"Substitution correspondence: {len(inventory)} model cases, {transformed} actual function results, "
          f"{native_commands} native commands passed.", flush=True)

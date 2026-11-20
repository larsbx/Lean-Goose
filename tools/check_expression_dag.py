"""Required expression-DAG proofs, independent model replay, and native scope probes."""
from __future__ import annotations

from copy import deepcopy
import gzip
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import sys
from typing import Callable

import expression_dag_profile as profile
import runtime
from check_stored_bindings import itf_value

LEAN_SOURCES = {"formal/lean/ExpressionDag.lean", "formal/lean/ExpressionDagAudit.lean",
                "formal/lean/ExpressionDagReplay.lean"}
QUINT_SOURCES = {"formal/quint/ExpressionDag.qnt"}
IMPLEMENTATIONS = {"tools/check_expression_dag.py", "tools/expression_dag_profile.py",
                   "formal/quint/dag_replay.py"}
DOCUMENTS = {"docs/expression-dag-scope.md", "schemas/expression-dag-replay-v1.md"}
LEAN_OBLIGATIONS = {"GooseExpressionDag." + name for name in (
    "decodeNode_sound", "decodeNode_complete", "decodeNode_success_iff_topological",
    "decode_sound", "decode_complete", "decode_length", "decode_success_iff_topological",
    "decode_rejects_non_topological", "topological_edges_decrease", "decoded_dag_has_no_cycles",
    "decode_append", "decode_prefix_extends", "decode_preserves_old_node", "decodeNode_append_preserves",
    "shared_application_decodes", "duplicated_children_decode_equally", "duplicate_node_decodes_same",
    "self_or_forward_reference_rejected", "scoped_iff_loose", "closed_iff_loose_zero", "scoped_monotone",
    "scopeCheck_correct", "lambda_scope_distinguishes_domain_and_body", "pi_scope_distinguishes_domain_and_body",
    "let_scope_distinguishes_value_and_body", "variable_requires_exact_depth", "height_positive",
    "child_height_lt", "refused_observation_is_empty", "observe_has_no_authority",
)}
QUINT_TESTS = {
    "emptyDagTest", "leafPayloadsTest", "applicationDecodeTest", "lambdaBinderTest", "piBinderTest",
    "letBinderTest", "openDomainNotBoundTest", "letValueNotBoundTest", "nestedBinderDecrementTest",
    "sharedOpenSubtreeDepthTest", "selfReferenceRefusalTest", "forwardReferenceRefusalTest",
    "escapingReferenceRefusalTest", "cyclicReferenceRefusalTest", "snapshotPrefixPreservedTest",
    "refusedDagHasNoExpressionsTest", "scopeDepthMonotoneTest", "exactHeightTest", "constantNamesLosslessTest",
    "dagAuthorityPreservedTest", "simulationBoundStuttersTest",
}
QUINT_OBLIGATIONS = {"ExpressionDag." + name for name in QUINT_TESTS | {"safety"}}
QUINT_REPLAY_CHUNK_SIZE = 256


def exact(actual: object, expected: object) -> bool:
    """Do not equate JSON booleans with integers in model or witness comparisons."""
    return json.dumps(actual, sort_keys=True, allow_nan=False) == json.dumps(expected, sort_keys=True, allow_nan=False)


def counterexample(exit_code: int, text: str, path: Path) -> None:
    if exit_code != 1 or "[violation] Found an issue" not in text or "error: Invariant violated" not in text:
        raise ValueError("incorrect binder decrement did not produce the designated invariant failure")
    witness = itf_value(json.loads(path.read_text()))
    states = witness.get("states", []) if isinstance(witness, dict) else []
    if not isinstance(states, list) or len(states) != 2 or any(not isinstance(state, dict) for state in states):
        raise ValueError("incorrect binder decrement did not produce its two-state witness")
    sort = {"tag": 0, "a": 0, "b": 0, "c": 0, "name": []}
    variable = {"tag": 1, "a": 1, "b": 0, "c": 0, "name": []}
    binder = {"tag": 4, "a": 0, "b": 1, "c": 0, "name": []}
    before = {"nodes": [sort, variable], "rows": [
        {"expression": [0, 0], "height": 1, "loose": 0},
        {"expression": [1, 1], "height": 1, "loose": 2}],
        "decoded": True, "acceptance_authority": False}
    after = deepcopy(before)
    after["nodes"].append(binder)
    after["rows"].append({"expression": [4, 0, 0, 1, 1], "height": 2, "loose": 0})
    if not exact(states[0].get("s"), before) or not exact(states[0].get("previous"), before) \
            or not exact(states[0].get("last"), variable) or states[0].get("hasStep") is not False \
            or not exact(states[1].get("s"), after) or not exact(states[1].get("previous"), before) \
            or not exact(states[1].get("last"), binder) or states[1].get("hasStep") is not True:
        raise ValueError("counterexample differs from the designated Var 1 binder-decrement mutation")


def compressed_input(path: Path, inputs: str) -> dict:
    encoded = inputs.encode()
    path.write_bytes(gzip.compress(encoded, mtime=0))
    return {"file": path.name, "encoding": "gzip", "sha256": runtime.sha256(path),
            "uncompressed_bytes": len(encoded), "uncompressed_sha256": hashlib.sha256(encoded).hexdigest()}


def replay(*, inventory: list[dict], label: str, output: Path, receipt: dict, lean_build: Path,
           lean: Path, lean_flags: list[str], env: dict, run: Callable) -> tuple[list[dict], dict]:
    inputs = "\n".join(profile.encode(case) for case in inventory) + "\n"
    input_record = compressed_input(output / f"dag-{label}-inputs.jsonl.gz", inputs)
    lean_results = profile.decode_models(run(
        [str(lean), *lean_flags, "--run", "ExpressionDagReplay.lean"], lean_build, output, receipt,
        f"dag-{label}-lean-replay", env=env, stdin=inputs, compress_log=True), inventory)
    chunks = []
    # A Quint REPL retains parsed source/history. Bound each fresh invocation's
    # input inventory, with sequential processes and no loss of replay coverage.
    for chunk_index, start in enumerate(range(0, len(inventory), QUINT_REPLAY_CHUNK_SIZE)):
        chunk = inventory[start:start + QUINT_REPLAY_CHUNK_SIZE]
        chunk_inputs = "\n".join(profile.encode(case) for case in chunk) + "\n"
        name = f"dag-{label}-quint-replay-{chunk_index:03d}"
        quint_results = profile.decode_models(run(
            [sys.executable, str(runtime.ROOT / "formal/quint/dag_replay.py")], runtime.ROOT, output, receipt,
            name, env=env, stdin=chunk_inputs, compress_log=True), chunk)
        if not exact(lean_results[start:start + len(chunk)], quint_results):
            raise ValueError(f"Lean and Quint disagree on {label} DAG expressions, heights, loose variables or scope at case {start}")
        chunks.append({"first_case_index": start, "case_count": len(chunk), "command_name": name,
                       "stdin_sha256": hashlib.sha256(chunk_inputs.encode()).hexdigest()})
    if sum(chunk["case_count"] for chunk in chunks) != len(inventory):
        raise ValueError("Quint replay chunks do not cover the complete ordered inventory")
    input_record.update(quint_replay_chunk_size=QUINT_REPLAY_CHUNK_SIZE, quint_replay_chunks=chunks)
    return lean_results, input_record


def execute(*, output: Path, receipt: dict, build: Path, lean_build: Path, lean: Path, lean_flags: list[str],
            quint: Path, binary: Path, env: dict, seed: str, run: Callable) -> None:
    lane = {"status": "running", "scope": "immutable raw DAG representation and binder scope; finite native correspondence",
            "acceptance_authority": False}
    receipt["expression_dag"] = lane
    inventory = profile.cases()
    if len(inventory) != profile.CASE_COUNT or len({case["id"] for case in inventory}) != profile.CASE_COUNT:
        raise ValueError("expression-DAG inventory differs from its declared finite bound")
    model = lean_build / "ExpressionDag.olean"
    run([str(lean), *lean_flags, "-o", str(model), "ExpressionDag.lean"], lean_build, output, receipt,
        "dag-lean-build", env=env)
    audit = run([str(lean), *lean_flags, "ExpressionDagAudit.lean"], lean_build, output, receipt,
                "dag-lean-axiom-audit", env=env)
    match = re.search(r"Expression DAG axiom audit passed: (\d+) required theorems without axioms; "
                      r"(\d+) declarations; (\d+) theorem declarations; support axioms: \[propext\]", audit)
    if match is None or int(match[1]) != len(LEAN_OBLIGATIONS):
        raise ValueError("expression-DAG audit did not confirm its entire required theorem inventory")
    lane["lean"] = {"status": "passed", "obligations": sorted(LEAN_OBLIGATIONS),
        "required_theorem_axioms": [], "namespace_support_axiom_allowlist": ["propext"],
        "namespace_declarations": int(match[2]), "namespace_theorem_declarations": int(match[3]),
        "compiled_model_sha256": runtime.sha256(model)}
    quint_root = runtime.ROOT / "formal/quint"
    run([str(quint), "typecheck", "ExpressionDag.qnt"], quint_root, output, receipt, "dag-quint-typecheck")
    tests = run([str(quint), "test", "ExpressionDag.qnt", "--backend=typescript",
                 "--max-samples=1", f"--seed={seed}"], quint_root, output, receipt, "dag-quint-tests")
    if "21 passing" not in tests or any(f"ok {name} passed 1 test(s)" not in tests for name in QUINT_TESTS):
        raise ValueError("Quint did not execute the complete expression-DAG deterministic test inventory")
    simulation = run([str(quint), "run", "ExpressionDag.qnt", "--backend=typescript",
        "--invariant=safety", "--max-samples=1000", "--max-steps=40", f"--seed={seed}", "--verbosity=1"],
        quint_root, output, receipt, "dag-quint-bounded-run")
    if "[ok] No violation found" not in simulation:
        raise ValueError("Quint did not complete its bounded expression-DAG invariant check")
    trace = output / "dag-quint-negative.itf.json"
    trace.unlink(missing_ok=True)
    run([str(quint), "run", "ExpressionDag.qnt", "--backend=typescript", "--init=unsafeInit",
        "--step=unsafeStep", "--invariant=safety", "--max-samples=1", "--max-steps=1",
        f"--seed={seed}", "--verbosity=2", "--out-itf", str(trace)], quint_root,
        output, receipt, "dag-quint-negative-control", expected_exit=1)
    counterexample(1, (output / "dag-quint-negative-control.log").read_text(), trace)
    lane["quint"] = {"status": "passed", "tests": sorted(QUINT_TESTS), "backend": "typescript",
        "invariant": "ExpressionDag.safety", "seed": seed, "max_samples": 1000, "max_steps": 40,
        "arena_node_bound": 8, "at_bound": "stutter", "leaf_payloads": [0, 1, 2, 3],
        "unbounded_proof": False, "negative_control": {"witnessed": True, "expected_exit_code": 1,
            "mutation": "Lam(Sort 0, Var 1) decrements body loose by two, falsely yielding zero instead of one",
            "trace": trace.name, "sha256": runtime.sha256(trace)}}
    predictions, inputs_record = replay(inventory=inventory, label="profile", output=output, receipt=receipt,
        lean_build=lean_build, lean=lean, lean_flags=lean_flags, env=env, run=run)
    descriptors = profile.probes(inventory)
    if len(descriptors) != profile.PROBE_COUNT or len({probe["id"] for probe in descriptors}) != profile.PROBE_COUNT:
        raise ValueError("native expression-DAG probe inventory differs from its declared bound")
    fixture = build / "expression-dag.tsv"
    comparison = output / "dag-native-comparison.jsonl.gz"
    observations = []
    native_commands = 0
    with comparison.open("wb") as raw, gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as zipped, \
            io.TextIOWrapper(zipped, encoding="utf-8", newline="\n") as log:
        for descriptor in descriptors:
            case = inventory[descriptor["case_index"]]
            prediction = predictions[descriptor["case_index"]]
            fixture.write_text(profile.native_fixture(case, descriptor["depth"]))
            results = {}
            for mode in (("--trace", "--check") if descriptor["check"] else ("--trace",)):
                result = subprocess.run([str(binary), mode, str(fixture)], cwd=runtime.ROOT,
                                        capture_output=True, text=True, timeout=15)
                results[mode] = {"exit_code": result.returncode, "stdout": result.stdout, "stderr": result.stderr}
                native_commands += 1
            log.write(json.dumps({"probe": descriptor, "input": case["model_input"],
                "fixture_sha256": runtime.sha256(fixture), "model": prediction,
                "native": results}, separators=(",", ":")) + "\n")
            observation = profile.check_native(case, descriptor["depth"], prediction, **results["--trace"])
            if descriptor["check"]:
                profile.check_observation(case, descriptor["depth"], observation, **results["--check"])
            observations.append(observation)
    if native_commands != profile.NATIVE_COMMAND_COUNT:
        raise ValueError("expression-DAG native command count differs from the declared profile")
    arena_inventory, mappings = profile.arena_cases(observations)
    if not arena_inventory or len(mappings) != len(observations):
        raise ValueError("observed native arenas are missing or not linked to every probe")
    arena_predictions, arena_inputs_record = replay(inventory=arena_inventory, label="arenas", output=output,
        receipt=receipt, lean_build=lean_build, lean=lean, lean_flags=lean_flags, env=env, run=run)
    arena_log = output / "dag-arena-comparison.jsonl.gz"
    snapshots, nodes, bindings, scope_checks = 0, 0, 0, 0
    with arena_log.open("wb") as raw, gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as zipped, \
            io.TextIOWrapper(zipped, encoding="utf-8", newline="\n") as log:
        for descriptor, observation, mapping in zip(descriptors, observations, mappings):
            case = inventory[descriptor["case_index"]]
            result = profile.compare_arenas(case, descriptor["depth"], predictions[descriptor["case_index"]],
                                           observation, [arena_predictions[index] for index in mapping])
            log.write(json.dumps({"probe": descriptor["id"], "arena_indices": mapping, "comparison": result},
                                 separators=(",", ":")) + "\n")
            snapshots += result["snapshots"]
            nodes += result["node_payloads"]
            bindings += result["binding_records"]
            scope_checks += result["native_scope_checked"]
    lane["finite_correspondence"] = {"status": "passed", "initial_model_cases": len(inventory),
        "topological_graphs": profile.FINITE_CASE_COUNT, "graph_node_lengths": [1, 2, 3],
        "leaves": ["Sort 0", "Sort 1", "Var 0", "Var 1", "Var 2", "Var 3", "Const missing"],
        "depths": list(profile.DEPTHS), "native_scope_probes": profile.FINITE_CASE_COUNT * len(profile.DEPTHS),
        "malformed_topology_controls": profile.MALFORMED_CASE_COUNT, "named_controls": profile.NAMED_CASE_COUNT,
        "empty_dag_model_only": True, "native_process_executions": native_commands,
        "unique_native_arenas_replayed": len(arena_inventory), "native_snapshots": snapshots,
        "native_node_payloads": nodes, "native_binding_records": bindings, "native_scope_checks": scope_checks,
        "lean_quint_full_model_agreement": True, "inputs": inputs_record, "arena_inputs": arena_inputs_record,
        "native_log": comparison.name, "native_log_sha256": runtime.sha256(comparison),
        "arena_comparison_log": arena_log.name, "arena_comparison_log_sha256": runtime.sha256(arena_log),
        "log_encoding": "gzip", "native_command_templates": [[str(binary), mode, str(fixture)] for mode in ("--trace", "--check")],
        "native_projection": "full raw DAGs, original decoded-node prefixes, immutable raw binding IDs and observable scope refusal or completion",
        "native_internal_free_or_height_observed": False, "universal_implementation_refinement": False,
        "bounds": {"native_arena_nodes": profile.MAX_ARENA_NODES, "structural_wire_tokens_per_request": profile.MAX_WIRE_TOKENS,
                   "model_line_bytes": profile.MAX_MODEL_LINE_BYTES}}
    lane["status"] = "passed"
    print(f"Expression-DAG correspondence: {len(inventory)} initial graphs, {len(arena_inventory)} native arenas, "
          f"{native_commands} native commands passed.", flush=True)

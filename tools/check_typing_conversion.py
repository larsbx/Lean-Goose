"""Fifth required formal scope: typing, conversion and compound stored fields."""
from __future__ import annotations

from copy import deepcopy
import json
from pathlib import Path
import subprocess
import sys
from typing import Callable

import runtime
import typing_conversion_profile as profile
from check_expression_dag import compressed_input
from check_stored_bindings import itf_value

LEAN_SOURCES = {"formal/lean/TypingConversion.lean", "formal/lean/TypingConversionAudit.lean",
                "formal/lean/TypingConversionReplay.lean"}
QUINT_SOURCES = {"formal/quint/TypingConversion.qnt"}
IMPLEMENTATIONS = {"tools/check_typing_conversion.py", "tools/typing_conversion_profile.py",
                   "formal/quint/typing_replay.py"}
DOCUMENTS = {"docs/typing-conversion.md", "schemas/typing-conversion-replay-v1.md"}
LEAN_OBLIGATIONS = {"GooseTypingConversion." + name for name in (
    "head_sound", "head_result_not_constant", "head_result_not_let", "normal_sound",
    "convertible_sound", "conversion_symmetric", "inference_and_sort_sound", "infer_sound",
    "sortLevel_sound", "checkValue_sound", "checked_success_has_semantics",
    "stored_inferred_converts_to_declared", "infer_sort_rule", "infer_variable_lifts_context",
    "infer_constant_uses_declared_type", "delta_uses_original_value",
    "zeta_uses_capture_avoiding_substitution", "beta_uses_capture_avoiding_substitution",
    "beta_substitution_preserves_scope", "pi_prop_is_impredicative", "pi_positive_is_max",
    "zero_budget_refuses_inference", "zero_budget_refuses_conversion", "duplicate_precedes_semantics",
    "refusal_preserves_all_bindings", "success_stores_exact_fields", "success_preserves_existing_prefix",
    "validate_unknown_constant", "unknown_zeta_value_is_not_erased",
    "unknown_beta_argument_is_not_erased", "run_has_no_authority", "fatal_step_stops_suffix",
)}
QUINT_TESTS = {
    "initialTypingStateTest", "sortInferenceTest", "lambdaInferenceTest", "betaValueRetainedTest",
    "betaDeclaredTypeRetainedTest", "zetaValueRetainedTest", "zetaDeclaredTypeRetainedTest",
    "storedAliasNormalizationTest", "constantUsesDeclaredTypeTest", "deltaUsesStoredValueTest",
    "erasedBetaUnknownRefusalTest", "erasedZetaUnknownRefusalTest", "expectedFunctionRefusalTest",
    "expectedSortRefusalTest", "finalConversionMismatchTest", "typedLetMismatchTest",
    "duplicatePreemptsScopeTest", "scopePreemptsUnknownTest", "refusalThenRetryTest",
    "fatalScopeAbsorbingTest", "dependentApplicationTest", "nestedCaptureAvoidanceTest",
    "impredicativePiTest", "modelFuelExhaustionTest", "headFuelBoundaryTest", "contextLookupLiftsTest",
}
QUINT_OBLIGATIONS = {"TypingConversion." + name for name in QUINT_TESTS | {"safety"}}
CASE_COUNT = 48
NATIVE_STEP_COUNT = 66
REFERENCE_CASE_COUNT = 44
REFERENCE_OUTCOME_COUNT = 59
SAMPLES = 1000
STEPS = 8


def counterexample(exit_code: int, text: str, path: Path) -> None:
    if type(exit_code) is not int or exit_code != 1 or "[violation] Found an issue" not in text \
            or "error: Invariant violated" not in text:
        raise ValueError("corrupt inferred field did not produce the designated invariant failure")
    witness = itf_value(profile.observations.json_object(path.read_text()))
    if set(witness) != {"#meta", "vars", "states"} or witness["vars"] != ["s", "previous", "last", "hasStep"] \
            or witness["#meta"].get("source") != "TypingConversion.qnt" \
            or witness["#meta"].get("status") != "violation" \
            or witness["#meta"].get("format") != "ITF" or len(witness["states"]) != 2:
        raise ValueError("typing counterexample has an unexpected source or state inventory")
    initial = {"environment": [], "snapshots": [], "halted": False, "acceptance_authority": False}
    name = [110, 48]
    default = {"name": name, "ty": [0, 1], "value": [0, 0], "fuel": 128}
    query = {"name": name, "ty": [5, 0, 1, 0, 1], "value": [4, 0, 1, 1, 0], "fuel": 128}
    wrong = {"name": name, "ty": query["ty"], "value": query["value"], "inferred": [0, 0]}
    corrupt = {"environment": [wrong], "snapshots": [{"name": name, "code": 0, "bindings": [wrong]}],
               "halted": False, "acceptance_authority": False}
    expected = [
        {"#meta": {"index": 0}, "s": initial, "previous": initial, "last": default, "hasStep": False},
        {"#meta": {"index": 1}, "s": corrupt, "previous": initial, "last": query, "hasStep": True},
    ]
    if not profile.exact(witness["states"], expected):
        raise ValueError("typing counterexample differs from exact identity-inferred-field corruption")


def malformed_requests() -> list[tuple[str, str]]:
    seed = deepcopy(profile.cases()[0].request)
    cases = [("empty-stream", ""), ("blank-line", "\n"), ("broken-json", "{\n")]

    def add(name: str, mutate: Callable) -> None:
        value = deepcopy(seed)
        mutate(value)
        cases.append((name, json.dumps(value, separators=(",", ":")) + "\n"))

    add("unknown-key", lambda q: q.update(extra=0))
    add("missing-key", lambda q: q.pop("fuel"))
    add("boolean-fuel", lambda q: q.update(fuel=True))
    add("negative-fuel", lambda q: q.update(fuel=-1))
    add("float-fuel", lambda q: q.update(fuel=128.0))
    add("excess-fuel", lambda q: q.update(fuel=257))
    add("empty-nodes", lambda q: q.update(nodes=[]))
    add("empty-definitions", lambda q: q.update(definitions=[]))
    add("excess-nodes", lambda q: q.update(nodes=[[0, 0, 0, 0, []]] * 129))
    add("excess-definitions", lambda q: q.update(definitions=q["definitions"] * 65))
    add("definition-selector-outside", lambda q: q["definitions"][0].__setitem__(1, len(q["nodes"])))
    add("boolean-selector", lambda q: q["definitions"][0].__setitem__(1, True))
    add("invalid-definition-name", lambda q: q["definitions"][0].__setitem__(0, [32]))
    add("self-reference", lambda q: q["nodes"].__setitem__(0, [3, 0, 0, 0, []]))
    add("noncanonical-unused-field", lambda q: q["nodes"][0].__setitem__(2, 1))
    add("unknown-tag", lambda q: q["nodes"][0].__setitem__(0, 7))
    add("boolean-payload", lambda q: q["nodes"][0].__setitem__(1, True))
    shared = [[0, 0, 0, 0, []]]
    for index in range(1, 17):
        shared.append([5, index - 1, index - 1, 0, []])
    cases.append(("shared-expansion-envelope", profile.encode({"nodes": shared,
                  "definitions": [[[120], 0, len(shared) - 1]], "fuel": 128}) + "\n"))
    encoded = profile.encode(seed)
    cases.append(("duplicate-key", encoded[:-1] + ',"fuel":128}\n'))
    cases.append(("nonfinite-fuel", encoded.replace('"fuel":128', '"fuel":NaN') + "\n"))
    cases.append(("exponent-fuel", encoded.replace('"fuel":128', '"fuel":128e0') + "\n"))
    return cases


def contract_controls(*, output: Path, receipt: dict, lean_build: Path, lean: Path,
                      lean_flags: list[str], env: dict, run: Callable) -> dict:
    commands = {
        "lean": ([str(lean), *lean_flags, "--run", "TypingConversionReplay.lean"], lean_build,
                 2, "invalid typing/conversion replay input:"),
        "quint": ([sys.executable, str(runtime.ROOT / "formal/quint/typing_replay.py")], runtime.ROOT,
                  1, "Quint typing replay failed:"),
    }
    malformed = malformed_requests()
    if len(malformed) != 24 or len({name for name, _ in malformed}) != 24:
        raise ValueError("typing malformed request inventory changed")
    record = compressed_input(output / "typing-malformed-inputs.jsonl.gz", "\n".join(
        json.dumps({"id": name, "stdin": stdin}, separators=(",", ":")) for name, stdin in malformed) + "\n")
    refusals = []
    for name, stdin in malformed:
        for engine, (command, cwd, code, diagnostic) in commands.items():
            label = f"typing-{engine}-reject-{name}"
            stdout = run(command, cwd, output, receipt, label, env=env, stdin=stdin, expected_exit=code)
            if stdout or not (output / f"{label}.log").read_text().startswith(diagnostic):
                raise ValueError(f"{engine} malformed typing request did not fail closed: {name}")
            refusals.append({"case": name, "engine": engine, "command_name": label, "exit_code": code})
    exhausted = deepcopy(profile.cases()[0])
    exhausted.name = "model_budget_exhaustion"
    exhausted.request["fuel"] = 0
    exhausted.expected.update(steps=[{"name": exhausted.request["definitions"][0][0],
                                     "outcome": 9, "bindings": []}], halted=True)
    stdin = profile.encode(exhausted.request) + "\n"
    exhaustion_input = compressed_input(output / "typing-budget-exhaustion.jsonl.gz", stdin)
    for engine, (command, cwd, _, _) in commands.items():
        text = run(command, cwd, output, receipt, f"typing-{engine}-model-exhaustion", env=env, stdin=stdin)
        profile.decode_models(text, [exhausted])
    return {"status": "passed", "malformed_cases": 24, "malformed_executions": len(refusals),
            "refusals": refusals, "inputs": record, "model_budget_control": exhaustion_input,
            "model_budget_code": 9, "model_budget_is_native_resource_limit": False}


def execute(*, output: Path, receipt: dict, build: Path, lean_build: Path, lean: Path,
            lean_flags: list[str], quint: Path, binary: Path, env: dict, seed: str, run: Callable) -> None:
    lane = {"status": "running", "universal_implementation_refinement": False,
            "native_resource_model": False, "lean": {}, "quint": {}}
    receipt["typing_conversion"] = lane
    model = lean_build / "TypingConversion.olean"
    run([str(lean), *lean_flags, "-o", str(model), "TypingConversion.lean"], lean_build,
        output, receipt, "typing-lean-build", env=env)
    audit = run([str(lean), *lean_flags, "TypingConversionAudit.lean"], lean_build,
                output, receipt, "typing-lean-axiom-audit", env=env)
    if "Typing/conversion axiom audit passed: 32 required theorems without axioms;" not in audit:
        raise ValueError("typing Lean audit did not confirm its complete required inventory")
    lane["lean"] = {"status": "passed", "obligations": sorted(LEAN_OBLIGATIONS),
                    "required_theorem_axioms": [], "namespace_support_axiom_allowlist": ["propext"],
                    "compiled_model_sha256": runtime.sha256(model)}
    quint_root = runtime.ROOT / "formal/quint"
    run([str(quint), "typecheck", "TypingConversion.qnt"], quint_root, output, receipt, "typing-quint-typecheck")
    tests = run([str(quint), "test", "TypingConversion.qnt", "--backend=typescript", "--max-samples=1",
                 "--match=^(" + "|".join(sorted(QUINT_TESTS)) + ")$",
                 f"--seed={seed}"], quint_root, output, receipt, "typing-quint-tests")
    if "26 passing" not in tests or any(f"ok {name} passed 1 test(s)" not in tests for name in QUINT_TESTS):
        raise ValueError("Quint did not execute the complete typing test inventory")
    simulation = run([str(quint), "run", "TypingConversion.qnt", "--backend=typescript", "--invariant=safety",
                      f"--max-samples={SAMPLES}", f"--max-steps={STEPS}", f"--seed={seed}", "--verbosity=1"],
                     quint_root, output, receipt, "typing-quint-bounded-run")
    if "[ok] No violation found" not in simulation:
        raise ValueError("Quint did not finish its bounded typing exploration")
    trace = output / "typing-quint-negative.itf.json"
    trace.unlink(missing_ok=True)
    run([str(quint), "run", "TypingConversion.qnt", "--backend=typescript", "--step=unsafeStep",
         "--invariant=safety", "--max-samples=1", "--max-steps=1", f"--seed={seed}",
         "--verbosity=2", "--out-itf", str(trace)], quint_root, output, receipt,
        "typing-quint-negative-control", expected_exit=1)
    counterexample(1, (output / "typing-quint-negative-control.log").read_text(), trace)
    lane["quint"] = {"status": "passed", "tests": sorted(QUINT_TESTS), "invariant": "safety",
                     "backend": "typescript", "seed": seed, "max_samples": SAMPLES, "max_steps": STEPS,
                     "maximum_processed_definitions": 4, "unbounded_proof": False,
                     "negative_control": {"witnessed": True, "trace": trace.name, "sha256": runtime.sha256(trace)},
                     "continuation_transition_cap": 2048, "harness_exhaustion_is_semantic_result": False}
    inventory = profile.cases()
    if len(inventory) != CASE_COUNT or sum(len(c.expected["steps"]) for c in inventory) != NATIVE_STEP_COUNT:
        raise ValueError("typing correspondence inventory changed")
    inputs = "\n".join(profile.encode(c.request) for c in inventory) + "\n"
    inputs_record = compressed_input(output / "typing-inputs.jsonl.gz", inputs)
    lean_results = profile.decode_models(run(
        [str(lean), *lean_flags, "--run", "TypingConversionReplay.lean"], lean_build, output, receipt,
        "typing-lean-replay", env=env, stdin=inputs, compress_log=True), inventory)
    quint_results = profile.decode_models(run(
        [sys.executable, str(quint_root / "typing_replay.py")], runtime.ROOT, output, receipt,
        "typing-quint-replay", env=env, stdin=inputs, compress_log=True), inventory)
    if not profile.exact(lean_results, quint_results):
        raise ValueError("Lean and Quint disagree on typing/conversion compound observations")
    lane["replay_contract"] = contract_controls(output=output, receipt=receipt, lean_build=lean_build,
                                               lean=lean, lean_flags=lean_flags, env=env, run=run)
    native_rows = []
    fixture = build / "typing.tsv"
    for item, expected in zip(inventory, lean_results):
        fixture.write_text(profile.fixture(item.request))
        observations = {}
        for mode in ("--trace", "--check"):
            command = [str(binary), mode, str(fixture)]
            result = subprocess.run(command, cwd=runtime.ROOT, capture_output=True, text=True, timeout=15)
            if mode == "--trace":
                profile.check_trace(item, expected, result.returncode, result.stdout, result.stderr)
            elif expected["halted"]:
                if result.returncode != 2 or result.stdout or result.stderr != "goose bounded checker: Invalid_scope\n":
                    raise ValueError("fatal typing check emitted a completed receipt or wrong exit")
            else:
                if result.returncode or result.stderr:
                    raise ValueError("typing check exited instead of producing semantic observations")
                outcomes = [{"name": bytes(s["name"]).decode("ascii"), "outcome": profile.OUTCOMES[s["outcome"]]}
                            for s in expected["steps"]]
                profile.observations.definition_observation("goose-aot", profile.observations.json_object(result.stdout), outcomes)
            observations[mode] = {"command": command, "exit_code": result.returncode,
                                  "stdout": result.stdout, "stderr": result.stderr}
        native_rows.append({"case": item.name, "purpose": item.purpose, "request": item.request,
                            "fixture": fixture.read_text(), "fixture_sha256": runtime.sha256(fixture),
                            "model": expected, "observations": observations})
    native_log = output / "typing-native-comparison.jsonl.gz"
    native_record = compressed_input(native_log, "\n".join(json.dumps(row, separators=(",", ":")) for row in native_rows) + "\n")
    lane["finite_correspondence"] = {"status": "passed", "cases": CASE_COUNT, "input_definitions": 67,
        "processed_snapshots": NATIVE_STEP_COUNT, "native_commands": 2 * CASE_COUNT,
        "lean_quint_authored_full_field_agreement": True, "model_recursion_budget": 128,
        "native_projection": "ordered outcomes, original type/value IDs, normalized inferred structures, immutable DAG and binding prefixes, fatal process status",
        "inputs": inputs_record, "log": native_record, "case_names": [c.name for c in inventory],
        "reference_engine_comparison_gate": "conformance.typing_conversion",
        "universal_implementation_refinement": False}
    lane["status"] = "passed"
    print(f"Typing/conversion: {CASE_COUNT} full-field native/model cases passed.", flush=True)


def check_reference_engines(binaries: dict, output: Path) -> dict:
    """Called within the existing source- and dependency-bound conformance gate."""
    inventory = [c for c in profile.cases() if c.lean_outcomes is not None]
    if len(inventory) != REFERENCE_CASE_COUNT \
            or sum(len(c.expected["steps"]) for c in inventory) != REFERENCE_OUTCOME_COUNT:
        raise ValueError("typing common-reference inventory changed")
    folder = output / "typing-conversion"
    folder.mkdir(exist_ok=True)
    rows = []
    for item in inventory:
        path = folder / (item.name + ".tsv")
        path.write_text(profile.fixture(item.request))
        engines = []
        for engine, key in (("goose-aot", "goose-aot"), ("lean-kernel", "lean-kernel"), ("ocaml-bytecode", "ocaml-check")):
            command = [str(binaries[key]), "--check", str(path)]
            result = subprocess.run(command, cwd=runtime.ROOT, capture_output=True, text=True, timeout=15)
            if result.returncode or result.stderr:
                raise ValueError(f"{engine} typing probe failed: {item.name}: {result.stderr}")
            observed = profile.observations.definition_observation(engine,
                profile.observations.json_object(result.stdout), profile.semantic_expectations(item, engine))
            engines.append({"observation": observed, "command": command, "exit_code": result.returncode,
                            "raw_stdout": result.stdout, "raw_stderr": result.stderr})
        rows.append({"case": item.name, "purpose": item.purpose, "fixture": path.relative_to(output).as_posix(),
                     "fixture_sha256": runtime.sha256(path), "engines": engines})
    return {"status": "passed", "cases": len(rows), "ordered_outcomes_per_engine": REFERENCE_OUTCOME_COUNT,
            "registered_semantic_disagreements": [],
            "comparison_scope": "definition success and designated semantic refusal; external drivers do not expose stored fields",
            "excluded_native_priority_and_fatal_cases": [c.name for c in profile.cases() if c.lean_outcomes is None],
            "observations": rows, "universal_implementation_refinement": False}

"""Required stored-binding proof, model replay, and native diagnostic lane."""
from __future__ import annotations

from copy import deepcopy
import gzip
import io
import json
from pathlib import Path
import re
import subprocess
import sys
from typing import Callable

import binding_trace_controls
import runtime
import stored_binding_profile as profile

LEAN_SOURCES = {"formal/lean/StoredBindings.lean", "formal/lean/StoredBindingsAudit.lean",
                "formal/lean/StoredBindingsReplay.lean"}
QUINT_SOURCES = {"formal/quint/StoredBindings.qnt"}
IMPLEMENTATIONS = {"tools/check_stored_bindings.py", "tools/stored_binding_profile.py",
                   "tools/binding_trace_controls.py", "formal/quint/stored_replay.py",
                   "tools/source_derivation.py", "reference/binding-trace.patch"}
LEAN_OBLIGATIONS = {"GooseStoredBindings." + name for name in (
    "lookup_latest_binding", "lookup_append_fresh_preserves_existing",
    "fresh_good_payload_exact", "fresh_alias_payload_exact", "duplicate_precedes_checks",
    "duplicate_preserves_environment", "mismatch_preserves_environment",
    "missing_alias_preserves_environment", "wrong_type_alias_preserves_environment",
    "initial_invariant", "step_preserves_invariant", "run_preserves_invariant",
    "run_success_names_exact", "run_environment_unique", "run_success_count_exact",
    "step_environment_extends", "run_environment_extends", "run_preserves_existing_binding",
    "run_preserves_existing_binding_fields", "step_preserves_existing_lookup",
    "run_preserves_existing_lookup", "run_preserves_name_uniqueness", "halted_step_identity",
    "halted_run_identity", "halted_no_receipt", "step_preserves_authority",
    "run_preserves_authority", "run_has_no_authority", "completed_receipt_has_no_authority",
)}
QUINT_TESTS = {
    "initialStoredStateTest", "goodPayloadLevelZeroTest", "goodPayloadLevelOneTest",
    "typedAliasPayloadTest", "wrongTypeAliasRefusalTest", "duplicatePreservesAllFieldsTest",
    "crossLevelDuplicateAliasTest", "mismatchPreservesAllFieldsTest", "unknownAliasPreservesAllFieldsTest",
    "refusalThenRetryTest", "levelOneAliasTest", "scopeSnapshotTest", "duplicatePreemptsScopeSnapshotTest",
    "haltStopsSnapshotsTest", "orderedSnapshotCountTest", "storedAuthorityPreservedTest",
}
QUINT_OBLIGATIONS = {"StoredBindings." + name for name in QUINT_TESTS | {"safety"}}


def itf_value(value: object) -> object:
    if isinstance(value, list):
        return [itf_value(item) for item in value]
    if isinstance(value, dict):
        if set(value) == {"#bigint"}:
            if not isinstance(value["#bigint"], str) or not re.fullmatch(r"0|[1-9][0-9]*", value["#bigint"]):
                raise ValueError("invalid natural number in stored-binding counterexample")
            return int(value["#bigint"])
        return {key: itf_value(item) for key, item in value.items()}
    return value


def counterexample(exit_code: int, text: str, path: Path) -> None:
    if exit_code != 1 or "[violation] Found an issue" not in text or "error: Invariant violated" not in text:
        raise ValueError("payload corruption did not produce the designated invariant failure")
    witness = itf_value(json.loads(path.read_text()))
    states = witness.get("states", []) if isinstance(witness, dict) else []
    if not isinstance(states, list) or len(states) != 2 or any(not isinstance(state, dict) for state in states):
        raise ValueError("payload corruption did not produce its two-state witness")
    binding = {"name": 0, "ty": [0, 1], "value": [0, 0], "inferred": [0, 1]}
    before = {"environment": [binding], "outcomes": [{"name": 0, "code": 0}], "halted": False,
              "acceptance_authority": False,
              "snapshots": [{"name": 0, "code": 0, "environment": [binding]}]}
    corrupted = dict(binding, value=[0, 999])
    after = deepcopy(before)
    after["environment"] = [corrupted]
    after["outcomes"].append({"name": 1, "code": 6})
    after["snapshots"].append({"name": 1, "code": 6, "environment": [corrupted]})
    def exact(actual: object, expected: object) -> bool:
        # Python's ordinary container equality equates False/0 and True/1.
        return json.dumps(actual, sort_keys=True, allow_nan=False) == json.dumps(expected, sort_keys=True, allow_nan=False)

    if not exact(states[0].get("s"), before) or not exact(states[0].get("previous"), before) \
            or states[0].get("hasStep") is not False or states[1].get("hasStep") is not True \
            or not exact(states[1].get("s"), after) or not exact(states[1].get("previous"), before) \
            or not exact(states[1].get("last"), {"kind": 1, "name": 1, "target": 0, "level": 0}):
        raise ValueError("counterexample differs from the designated existing-value corruption on refusal")


def execute(*, output: Path, receipt: dict, build: Path, lean_build: Path, lean: Path, lean_flags: list[str],
            quint: Path, binary: Path, env: dict, seed: str, run: Callable) -> None:
    lane = {"status": "running", "scope": "full stored records; finite native Sort/Const profile",
            "acceptance_authority": False}
    receipt["stored_bindings"] = lane
    inventory = profile.cases()
    if len(inventory) != profile.CASE_COUNT or len(set(inventory)) != profile.CASE_COUNT:
        raise ValueError("stored-binding inventory differs from its declared finite bound")
    inputs = "\n".join(profile.encode(actions) for actions in inventory) + "\n"
    inputs_path = output / "stored-binding-inputs.txt"
    inputs_path.write_text(inputs)
    model = lean_build / "StoredBindings.olean"
    run([str(lean), *lean_flags, "-o", str(model), "StoredBindings.lean"], lean_build, output, receipt,
        "stored-lean-build", env=env)
    audit = run([str(lean), *lean_flags, "StoredBindingsAudit.lean"], lean_build, output, receipt,
                "stored-lean-axiom-audit", env=env)
    match = re.search(r"Stored binding axiom audit passed: (\d+) required theorems without axioms; "
                      r"(\d+) declarations; (\d+) theorem declarations; support axioms: \[propext\]", audit)
    if match is None or int(match[1]) != len(LEAN_OBLIGATIONS):
        raise ValueError("stored-binding audit did not confirm its entire required theorem inventory")
    lane["lean"] = {"status": "passed", "obligations": sorted(LEAN_OBLIGATIONS),
        "required_theorem_axioms": [], "namespace_support_axiom_allowlist": ["propext"],
        "namespace_declarations": int(match[2]), "namespace_theorem_declarations": int(match[3]),
        "compiled_model_sha256": runtime.sha256(model)}
    lean_results = profile.decode_models(run([str(lean), *lean_flags, "--run", "StoredBindingsReplay.lean"], lean_build,
        output, receipt, "stored-lean-replay", env=env, stdin=inputs, compress_log=True), inventory)
    quint_root = runtime.ROOT / "formal/quint"
    run([str(quint), "typecheck", "StoredBindings.qnt"], quint_root, output, receipt, "stored-quint-typecheck")
    tests = run([str(quint), "test", "StoredBindings.qnt", "--backend=typescript",
                 "--max-samples=1", f"--seed={seed}"], quint_root, output, receipt, "stored-quint-tests")
    if "16 passing" not in tests or any(f"ok {name} passed 1 test(s)" not in tests for name in QUINT_TESTS):
        raise ValueError("Quint did not execute the complete stored-binding deterministic test inventory")
    simulation = run([str(quint), "run", "StoredBindings.qnt", "--backend=typescript",
        "--invariant=safety", "--max-samples=1000", "--max-steps=40", f"--seed={seed}", "--verbosity=1"],
        quint_root, output, receipt, "stored-quint-bounded-run")
    if "[ok] No violation found" not in simulation:
        raise ValueError("Quint did not complete its bounded stored-binding invariant check")
    trace = output / "stored-quint-negative.itf.json"
    trace.unlink(missing_ok=True)
    run([str(quint), "run", "StoredBindings.qnt", "--backend=typescript", "--init=unsafeInit",
        "--step=unsafeStep", "--invariant=safety", "--max-samples=1", "--max-steps=1",
        f"--seed={seed}", "--verbosity=2", "--out-itf", str(trace)], quint_root,
        output, receipt, "stored-quint-negative-control", expected_exit=1)
    counterexample(1, (output / "stored-quint-negative-control.log").read_text(), trace)
    quint_results = profile.decode_models(run([sys.executable, str(quint_root / "stored_replay.py")],
        runtime.ROOT, output, receipt, "stored-quint-replay", env=env, stdin=inputs, compress_log=True), inventory)
    if lean_results != quint_results:
        raise ValueError("Lean and Quint disagree on a stored record, outcome, or snapshot")
    lane["quint"] = {"status": "passed", "tests": sorted(QUINT_TESTS), "backend": "typescript",
        "invariant": "StoredBindings.safety", "seed": seed, "max_samples": 1000, "max_steps": 40,
        "unbounded_proof": False, "negative_control": {"witnessed": True, "expected_exit_code": 1,
            "mutation": "existing value [0,0] becomes [0,999] on a Type_mismatch refusal",
            "trace": trace.name, "sha256": runtime.sha256(trace)}}
    comparison = output / "stored-native-comparison.jsonl.gz"
    fixture = build / "stored-bindings.tsv"
    completed, halted, snapshots = 0, 0, 0
    with comparison.open("wb") as raw, gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as zipped, \
            io.TextIOWrapper(zipped, encoding="utf-8", newline="\n") as log:
        for index, (actions, prediction) in enumerate(zip(inventory, lean_results)):
            fixture.write_text(profile.fixture(actions))
            results = {}
            for mode in ("--trace", "--check"):
                result = subprocess.run([str(binary), mode, str(fixture)], cwd=runtime.ROOT,
                                        capture_output=True, text=True, timeout=15)
                results[mode] = {"exit_code": result.returncode, "stdout": result.stdout, "stderr": result.stderr}
            log.write(json.dumps({"case": index, "input": profile.encode(actions),
                "fixture_sha256": runtime.sha256(fixture), "model": prediction,
                "native": results}, separators=(",", ":")) + "\n")
            profile.check_trace(prediction, actions, **results["--trace"])
            profile.check_observation(prediction, **results["--check"])
            completed += not prediction["halted"]
            halted += prediction["halted"]
            snapshots += len(prediction["snapshots"])
    if (completed, halted, snapshots) != (2032, 922, 7546):
        raise ValueError("stored-binding native partition differs from the declared replay profile")
    lane["finite_correspondence"] = {"status": "passed", "cases": len(inventory),
        "action_count": len(profile.ACTIONS), "names": [0, 1], "declared_sort_levels": [0, 1],
        "trace_lengths": [1, 2, 3], "completed_traces_and_receipts": completed,
        "designated_scope_failures": halted, "binding_snapshots": snapshots,
        "native_process_executions": 2 * len(inventory), "lean_quint_full_model_agreement": True,
        "native_projection": "every full stored binding payload and snapshot; raw old binding IDs and immutable node prefix; existing --check observations",
        "universal_implementation_refinement": False, "inputs": inputs_path.name,
        "inputs_sha256": runtime.sha256(inputs_path), "log": comparison.name,
        "log_encoding": "gzip", "log_sha256": runtime.sha256(comparison),
        "native_command_templates": [[str(binary), mode, str(fixture)] for mode in ("--trace", "--check")]}
    lane["native_diagnostic_controls"] = binding_trace_controls.run_controls(binary, build, output)
    lane["status"] = "passed"
    print(f"Stored-binding correspondence: {len(inventory)} traces, {snapshots} snapshots passed.", flush=True)

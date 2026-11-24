"""Sixth formal scope: semantic environments, typed context weakening, and record projection."""
from __future__ import annotations

import json
from pathlib import Path
import subprocess
import sys
from typing import Callable

import runtime
import semantic_environment_profile as histories
import typing_conversion_profile as profile
from check_expression_dag import compressed_input
from semantic_environment_negative import counterexample

LEAN_SOURCES = {"formal/lean/EnvironmentScope.lean", "formal/lean/SemanticEnvironment.lean",
                "formal/lean/ContextWeakening.lean", "formal/lean/ContextWeakeningControls.lean",
                "formal/lean/SemanticEnvironmentAudit.lean"}
QUINT_SOURCES = {"formal/quint/SemanticEnvironment.qnt"}
IMPLEMENTATIONS = {"tools/check_semantic_environment.py", "tools/semantic_environment_profile.py",
                   "tools/semantic_environment_negative.py"}
DOCUMENTS = {"docs/semantic-environment.md", "docs/context-weakening.md"}
LEAN_OBLIGATIONS = {"GooseSemanticEnvironment." + name for name in (
    "validate_implies_available", "available_monotone", "lookup_extends_reflexive",
    "lookup_extends_transitive", "find_snoc", "fresh_append_extends", "find_latest",
    "head_reduction_weaken", "normalization_weaken", "conversion_weaken", "inference_weaken",
    "sort_weaken", "binding_valid_weaken", "checked_success_preconditions",
    "checked_success_certifies_binding", "successful_insertion_certified",
    "refusal_retains_certificate", "step_preserves_certification", "step_preserves_lookup",
    "certified_lookup_valid", "certified_lookup_has_closed_originals", "certified_lookup_conversion",
    "run_snapshots_certified", "certified_snapshots_end", "run_final_environment_certified",
    "empty_run_has_semantic_environment", "run_preserves_lookup", "run_preserves_semantic_judgments",
    "step_environment_prefix", "run_environment_prefix", "project_binding_fields", "project_append",
    "project_successful_insertion", "project_refusal_preserves_records", "projected_lookup_corresponds",
    "projected_trace_preserves_old_record", "projected_trace_preserves_lookup",
)} | {"GooseEnvironmentScope." + name for name in (
    "lookup_values_closed_of_certified",
    "head_preserves_scope",
    "normalization_preserves_scope",
    "normalization_yields_normal_form",
    "normalization_fixes_normal_form",
    "normal_form_available",
    "converted_normal_form_preserves_scope",
    "binding_valid_inferred_closed_available",
    "checked_success_inferred_scope_of_closed_values",
    "checked_success_inferred_closed_available",
    "ContextValid.scoped",
    "lift_preserves_available",
    "substitution_preserves_available",
    "head_preserves_available",
    "scoped_context_lifts_lookup",
    "inference_preserves_scope_available",
    "valid_context_inference_scope",
    "certified_lookup_all_fields",
    "certified_record_lookup",
    "run_snapshots_all_fields",
    "run_final_environment_all_fields",
    "malformed_delta_value_escapes",
    "closed_delta_values_allow_scope_of_normalized_field",
    "dependent_context_valid_and_lifts",
    "self_scoped_context_refused",
    "scoped_context_can_lack_sort",
    "conversion_refusal_does_not_insert",
)} | {"GooseContextWeakening." + name for name in (
    "lift_after_lift", "lift_after_substitute", "head_reduction_lift", "normalization_lift",
    "conversion_lift", "ContextInsertion.cutoff_length", "ContextInsertion.lookup_lift",
    "inference_lift", "sort_lift", "ContextInsertion.preserves_valid", "substitution_hit",
    "literal_beta_premises", "zeta_inference", "zeta_sort",
    "middle_insertion_transports_dependent_lookup", "middle_insertion_transports_dependent_application",
    "deep_insertion_transports_let_sort", "stale_annotation_scoped_but_invalid",
    "self_referential_insertion_refused", "unsorted_insertion_refused",
    "open_constant_type_breaks_weakening", "open_delta_value_breaks_reduction_lift",
    "literal_beta_requires_conversion", "substitution_can_unblock_neutral_head",
)}
QUINT_TESTS = {
    "emptySemanticHistoryTest", "firstPredecessorIsEmptyTest", "compoundCertificateTest",
    "predecessorMatchesExactPrefixTest", "threeSuccessfulSemanticRecordsTest",
    "previousSemanticRecordPreservedTest", "previousLookupPreservedTest", "semanticWeakeningObservedTest",
    "projectedPayloadsExactTest", "projectedLookupExactTest", "projectedUnknownLookupTest",
    "projectedNameLengthDistinctTest", "mismatchPreservesSemanticHistoryTest",
    "unknownPreservesSemanticHistoryTest", "duplicatePreservesSemanticHistoryTest",
    "duplicateBeforeScopeAndBudgetTest", "rejectedNameCanBeRetriedTest",
    "forwardReferenceCannotCertifyTest", "selfReferenceCannotCertifyTest",
    "fatalScopePreservesHistoryTest", "fatalBudgetPreservesHistoryTest",
    "haltedSuffixHasNoCertificateTest", "betaValueCertificateTest", "zetaValueCertificateTest",
    "forgedDeltaValueProducesOpenFieldTest",
    "closedDeltaSeparatesStoredFromRawInferenceTest",
    "dependentBinderOuterTailScopeTest",
    "malformedBinderCannotBeItsOwnTypeContextTest",
    "scopedContextWithoutSortTest",
    "conversionRefusalKeepsInferredFieldAndNameFreeTest",
    "dependentNormalizationScopeOnExtensionTest",
}
QUINT_OBLIGATIONS = {"SemanticEnvironment." + name for name in QUINT_TESTS | {"safety"}}
SAMPLES = 1000
STEPS = 8
SEED = "20261123"


def execute(*, output: Path, receipt: dict, build: Path, lean_build: Path, lean: Path,
            lean_flags: list[str], quint: Path, binary: Path, env: dict, run: Callable) -> None:
    lane: dict = {"status": "running", "implementation_refinement": False,
                  "scope": "certified environments, structural scope, typed context weakening, and complete records"}
    receipt["semantic_environment"] = lane
    model = lean_build / "SemanticEnvironment.olean"
    run([str(lean), *lean_flags, "-o", str(model), "SemanticEnvironment.lean"], lean_build,
        output, receipt, "environment-lean-build", env=env)
    scope_model = lean_build / "EnvironmentScope.olean"
    run([str(lean), *lean_flags, "-o", str(scope_model), "EnvironmentScope.lean"], lean_build,
        output, receipt, "environment-scope-lean-build", env=env)
    weakening_model = lean_build / "ContextWeakening.olean"
    run([str(lean), *lean_flags, "-o", str(weakening_model), "ContextWeakening.lean"], lean_build,
        output, receipt, "context-weakening-lean-build", env=env)
    weakening_controls = lean_build / "ContextWeakeningControls.olean"
    run([str(lean), *lean_flags, "-o", str(weakening_controls), "ContextWeakeningControls.lean"], lean_build,
        output, receipt, "context-weakening-controls-lean-build", env=env)
    audit = run([str(lean), *lean_flags, "SemanticEnvironmentAudit.lean"], lean_build,
                output, receipt, "environment-lean-axiom-audit", env=env)
    if f"Semantic environment axiom audit passed: {len(LEAN_OBLIGATIONS)} required theorems without axioms;" not in audit:
        raise ValueError("semantic environment Lean audit did not confirm its required inventory")
    lane["lean"] = {"status": "passed", "obligations": sorted(LEAN_OBLIGATIONS),
                    "required_theorem_axioms": [], "namespace_support_axiom_allowlist": ["propext"],
                    "compiled_model_sha256": runtime.sha256(model),
                    "compiled_scope_model_sha256": runtime.sha256(scope_model),
                    "compiled_context_weakening_sha256": runtime.sha256(weakening_model),
                    "compiled_context_weakening_controls_sha256": runtime.sha256(weakening_controls),
                    "inferred_field_scope_premise": "closed original values of bindings selected by lookup",
                    "semantic_predicate": "independent HasSort/Infers/Normalizes/Converts judgments and closed, available original syntax",
                    "record_bridge": "exact encoded payloads; lookup correspondence assumes injective name coding",
                    "old_four_action_checker_simulation": False}
    quint_root = runtime.ROOT / "formal/quint"
    run([str(quint), "typecheck", "SemanticEnvironment.qnt"], quint_root,
        output, receipt, "environment-quint-typecheck")
    tests = run([str(quint), "test", "SemanticEnvironment.qnt", "--backend=typescript", "--max-samples=1",
                 "--match=^(" + "|".join(sorted(QUINT_TESTS)) + ")$", f"--seed={SEED}"],
                quint_root, output, receipt, "environment-quint-tests")
    if f"{len(QUINT_TESTS)} passing" not in tests \
            or any(f"ok {name} passed 1 test(s)" not in tests for name in QUINT_TESTS):
        raise ValueError("Quint did not execute the complete semantic environment test inventory")
    simulation = run([str(quint), "run", "SemanticEnvironment.qnt", "--backend=typescript",
                      "--invariant=safety", f"--max-samples={SAMPLES}", f"--max-steps={STEPS}",
                      f"--seed={SEED}", "--verbosity=1"], quint_root, output, receipt,
                     "environment-quint-bounded-run")
    if "[ok] No violation found" not in simulation:
        raise ValueError("Quint did not complete bounded semantic environment exploration")
    trace = output / "environment-quint-negative.itf.json"
    trace.unlink(missing_ok=True)
    run([str(quint), "run", "SemanticEnvironment.qnt", "--backend=typescript",
         "--init=negativeInit", "--step=unsafeStep", "--invariant=safety", "--max-samples=1",
         "--max-steps=1", f"--seed={SEED}", "--verbosity=2", "--out-itf", str(trace)],
        quint_root, output, receipt, "environment-quint-negative-control", expected_exit=1)
    counterexample(1, (output / "environment-quint-negative-control.log").read_text(), trace)
    lane["quint"] = {"status": "passed", "tests": sorted(QUINT_TESTS), "invariant": "safety",
        "backend": "typescript", "seed": SEED, "max_samples": SAMPLES, "max_steps": STEPS,
        "maximum_processed_definitions": 4, "names": 3, "input_forms": 9,
        "unbounded_proof": False, "independent_semantic_correctness_proof": False,
        "certificate_checks": "frozen predecessor and fields plus separately evaluated semantic witness equations",
        "negative_control": {"witnessed": True, "trace": trace.name, "sha256": runtime.sha256(trace)}}

    inventory = histories.cases()
    inputs = "\n".join(profile.encode(item.request) for item in inventory) + "\n"
    inputs_record = compressed_input(output / "environment-inputs.jsonl.gz", inputs)
    lean_results = profile.decode_models(run(
        [str(lean), *lean_flags, "--run", "TypingConversionReplay.lean"], lean_build,
        output, receipt, "environment-lean-replay", env=env, stdin=inputs, compress_log=True), inventory)
    quint_results = profile.decode_models(run(
        [sys.executable, str(quint_root / "typing_replay.py")], runtime.ROOT,
        output, receipt, "environment-quint-replay", env=env, stdin=inputs, compress_log=True), inventory)
    if not profile.exact(lean_results, quint_results):
        raise ValueError("Lean and Quint disagree on semantic environment history observations")
    native_rows = []
    fixture = build / "semantic-environment.tsv"
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
                    raise ValueError("fatal environment history emitted a completed receipt or wrong exit")
            else:
                if result.returncode or result.stderr:
                    raise ValueError("environment history check exited instead of producing observations")
                outcomes = [{"name": bytes(s["name"]).decode("ascii"), "outcome": profile.OUTCOMES[s["outcome"]]}
                            for s in expected["steps"]]
                profile.observations.definition_observation("goose-aot", profile.observations.json_object(result.stdout), outcomes)
            observations[mode] = {"command": command, "exit_code": result.returncode,
                                  "stdout": result.stdout, "stderr": result.stderr}
        native_rows.append({"case": item.name, "purpose": item.purpose, "request": item.request,
                            "fixture": fixture.read_text(), "fixture_sha256": runtime.sha256(fixture),
                            "model": expected, "observations": observations})
    native_record = compressed_input(output / "environment-native-comparison.jsonl.gz",
        "\n".join(json.dumps(row, separators=(",", ":")) for row in native_rows) + "\n")
    lane["finite_correspondence"] = {"status": "passed", "cases": histories.CASE_COUNT,
        "input_definitions": histories.INPUT_DEFINITIONS, "processed_snapshots": histories.PROCESSED_SNAPSHOTS,
        "native_commands": 2 * histories.CASE_COUNT, "model_recursion_budget": 128,
        "lean_quint_authored_full_field_agreement": True,
        "replay_semantics": "unchanged actual typing/conversion evaluators",
        "native_projection": "ordered full records, original type/value IDs, inferred structures, immutable prefixes, fatal status",
        "semantic_certificates_observed_from_native": False,
        "inputs": inputs_record, "log": native_record, "case_names": [item.name for item in inventory],
        "reference_engine_comparison_gate": "conformance.semantic_environment",
        "universal_implementation_refinement": False}
    lane["status"] = "passed"
    print(f"Semantic environments: {histories.CASE_COUNT} native/model histories passed.", flush=True)


def check_reference_engines(binaries: dict, output: Path) -> dict:
    """Add separate ordered outcomes without changing the earlier finite lanes."""
    all_cases = histories.cases()
    inventory = [item for item in all_cases if item.lean_outcomes is not None]
    folder = output / "semantic-environment"
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
                raise ValueError(f"{engine} semantic environment probe failed: {item.name}: {result.stderr}")
            observed = profile.observations.definition_observation(engine,
                profile.observations.json_object(result.stdout), profile.semantic_expectations(item, engine))
            engines.append({"observation": observed, "command": command, "exit_code": result.returncode,
                            "raw_stdout": result.stdout, "raw_stderr": result.stderr})
        rows.append({"case": item.name, "purpose": item.purpose, "fixture": path.relative_to(output).as_posix(),
                     "fixture_sha256": runtime.sha256(path), "engines": engines})
    return {"status": "passed", "cases": len(rows), "ordered_outcomes_per_engine": histories.REFERENCE_OUTCOMES,
            "registered_semantic_disagreements": [],
            "comparison_scope": "ordered success/refusal histories; external drivers expose no stored fields or semantic certificates",
            "excluded_native_priority_and_fatal_cases": [item.name for item in all_cases if item.lean_outcomes is None],
            "observations": rows, "universal_implementation_refinement": False}

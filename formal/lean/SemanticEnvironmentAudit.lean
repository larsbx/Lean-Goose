import Lean.Elab.Command
import Lean.Util.CollectAxioms
import ContextWeakeningControls

open Lean Elab Command

/- Audit every declaration in the new namespace, not just a sample. The named
obligations must have empty transitive axiom closures. Generated support alone
may use the explicitly allowed proposition-extensionality axiom. -/
elab "audit_goose_semantic_environment" : command => do
  let env ← getEnv
  let required : Array Name := #[
    ``GooseSemanticEnvironment.validate_implies_available,
    ``GooseSemanticEnvironment.available_monotone,
    ``GooseSemanticEnvironment.lookup_extends_reflexive,
    ``GooseSemanticEnvironment.lookup_extends_transitive,
    ``GooseSemanticEnvironment.find_snoc,
    ``GooseSemanticEnvironment.fresh_append_extends,
    ``GooseSemanticEnvironment.find_latest,
    ``GooseSemanticEnvironment.head_reduction_weaken,
    ``GooseSemanticEnvironment.normalization_weaken,
    ``GooseSemanticEnvironment.conversion_weaken,
    ``GooseSemanticEnvironment.inference_weaken,
    ``GooseSemanticEnvironment.sort_weaken,
    ``GooseSemanticEnvironment.binding_valid_weaken,
    ``GooseSemanticEnvironment.checked_success_preconditions,
    ``GooseSemanticEnvironment.checked_success_certifies_binding,
    ``GooseSemanticEnvironment.successful_insertion_certified,
    ``GooseSemanticEnvironment.refusal_retains_certificate,
    ``GooseSemanticEnvironment.step_preserves_certification,
    ``GooseSemanticEnvironment.step_preserves_lookup,
    ``GooseSemanticEnvironment.certified_lookup_valid,
    ``GooseSemanticEnvironment.certified_lookup_has_closed_originals,
    ``GooseSemanticEnvironment.certified_lookup_conversion,
    ``GooseSemanticEnvironment.run_snapshots_certified,
    ``GooseSemanticEnvironment.certified_snapshots_end,
    ``GooseSemanticEnvironment.run_final_environment_certified,
    ``GooseSemanticEnvironment.empty_run_has_semantic_environment,
    ``GooseSemanticEnvironment.run_preserves_lookup,
    ``GooseSemanticEnvironment.run_preserves_semantic_judgments,
    ``GooseSemanticEnvironment.step_environment_prefix,
    ``GooseSemanticEnvironment.run_environment_prefix,
    ``GooseSemanticEnvironment.project_binding_fields,
    ``GooseSemanticEnvironment.project_append,
    ``GooseSemanticEnvironment.project_successful_insertion,
    ``GooseSemanticEnvironment.project_refusal_preserves_records,
    ``GooseSemanticEnvironment.projected_lookup_corresponds,
    ``GooseSemanticEnvironment.projected_trace_preserves_old_record,
    ``GooseSemanticEnvironment.projected_trace_preserves_lookup,
    ``GooseEnvironmentScope.lookup_values_closed_of_certified,
    ``GooseEnvironmentScope.head_preserves_scope,
    ``GooseEnvironmentScope.normalization_preserves_scope,
    ``GooseEnvironmentScope.normalization_yields_normal_form,
    ``GooseEnvironmentScope.normalization_fixes_normal_form,
    ``GooseEnvironmentScope.normal_form_available,
    ``GooseEnvironmentScope.converted_normal_form_preserves_scope,
    ``GooseEnvironmentScope.binding_valid_inferred_closed_available,
    ``GooseEnvironmentScope.checked_success_inferred_scope_of_closed_values,
    ``GooseEnvironmentScope.checked_success_inferred_closed_available,
    ``GooseEnvironmentScope.ContextValid.scoped,
    ``GooseEnvironmentScope.lift_preserves_available,
    ``GooseEnvironmentScope.substitution_preserves_available,
    ``GooseEnvironmentScope.head_preserves_available,
    ``GooseEnvironmentScope.scoped_context_lifts_lookup,
    ``GooseEnvironmentScope.inference_preserves_scope_available,
    ``GooseEnvironmentScope.valid_context_inference_scope,
    ``GooseEnvironmentScope.certified_lookup_all_fields,
    ``GooseEnvironmentScope.certified_record_lookup,
    ``GooseEnvironmentScope.run_snapshots_all_fields,
    ``GooseEnvironmentScope.run_final_environment_all_fields,
    ``GooseEnvironmentScope.malformed_delta_value_escapes,
    ``GooseEnvironmentScope.closed_delta_values_allow_scope_of_normalized_field,
    ``GooseEnvironmentScope.dependent_context_valid_and_lifts,
    ``GooseEnvironmentScope.self_scoped_context_refused,
    ``GooseEnvironmentScope.scoped_context_can_lack_sort,
    ``GooseEnvironmentScope.conversion_refusal_does_not_insert,
    ``GooseContextWeakening.lift_after_lift,
    ``GooseContextWeakening.lift_after_substitute,
    ``GooseContextWeakening.head_reduction_lift,
    ``GooseContextWeakening.normalization_lift,
    ``GooseContextWeakening.conversion_lift,
    ``GooseContextWeakening.ContextInsertion.cutoff_length,
    ``GooseContextWeakening.ContextInsertion.lookup_lift,
    ``GooseContextWeakening.inference_lift,
    ``GooseContextWeakening.sort_lift,
    ``GooseContextWeakening.ContextInsertion.preserves_valid,
    ``GooseContextWeakening.substitution_hit,
    ``GooseContextWeakening.literal_beta_premises,
    ``GooseContextWeakening.zeta_inference,
    ``GooseContextWeakening.zeta_sort,
    ``GooseContextWeakening.middle_insertion_transports_dependent_lookup,
    ``GooseContextWeakening.middle_insertion_transports_dependent_application,
    ``GooseContextWeakening.deep_insertion_transports_let_sort,
    ``GooseContextWeakening.stale_annotation_scoped_but_invalid,
    ``GooseContextWeakening.self_referential_insertion_refused,
    ``GooseContextWeakening.unsorted_insertion_refused,
    ``GooseContextWeakening.open_constant_type_breaks_weakening,
    ``GooseContextWeakening.open_delta_value_breaks_reduction_lift,
    ``GooseContextWeakening.literal_beta_requires_conversion,
    ``GooseContextWeakening.substitution_can_unblock_neutral_head]
  for name in required do
    match env.find? name with
    | none => throwError "missing semantic_environment obligation: {name}"
    | some info =>
      unless info.isTheorem do
        throwError "semantic_environment obligation is not a theorem: {name}"
      let axioms ← collectAxioms name
      unless axioms.isEmpty do
        throwError "required semantic environment theorem depends on axioms: {name}: {axioms}"
  let allowed : Array Name := #[``propext]
  let mut used : Array Name := #[]
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  for (name, info) in env.constants.toList do
    let userName := (privateToUserName? name).getD name
    if (`GooseSemanticEnvironment).isPrefixOf userName || (`GooseEnvironmentScope).isPrefixOf userName ||
        (`GooseContextWeakening).isPrefixOf userName then
      declarations := declarations + 1
      if info.isTheorem then theorems := theorems + 1
      let axioms ← collectAxioms name
      for axiomName in axioms do
        if !used.contains axiomName then used := used.push axiomName
        unless allowed.contains axiomName do
          throwError "semantic_environment namespace axiom audit rejected {name}: {axiomName}"
  logInfo m!"Semantic environment axiom audit passed: {required.size} required theorems without axioms; {declarations} declarations; {theorems} theorem declarations; support axioms: {used}"

audit_goose_semantic_environment

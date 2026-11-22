import Lean.Elab.Command
import Lean.Util.CollectAxioms
import TypingConversion

open Lean Elab Command

/- Audit every declaration in the new namespace, not just a sample. The named
obligations must have empty transitive axiom closures. Generated support alone
may use the explicitly allowed proposition-extensionality axiom. -/
elab "audit_goose_typing_conversion" : command => do
  let env ← getEnv
  let required : Array Name := #[
    ``GooseTypingConversion.head_sound,
    ``GooseTypingConversion.head_result_not_constant,
    ``GooseTypingConversion.head_result_not_let,
    ``GooseTypingConversion.normal_sound,
    ``GooseTypingConversion.convertible_sound,
    ``GooseTypingConversion.conversion_symmetric,
    ``GooseTypingConversion.inference_and_sort_sound,
    ``GooseTypingConversion.infer_sound,
    ``GooseTypingConversion.sortLevel_sound,
    ``GooseTypingConversion.checkValue_sound,
    ``GooseTypingConversion.checked_success_has_semantics,
    ``GooseTypingConversion.stored_inferred_converts_to_declared,
    ``GooseTypingConversion.infer_sort_rule,
    ``GooseTypingConversion.infer_variable_lifts_context,
    ``GooseTypingConversion.infer_constant_uses_declared_type,
    ``GooseTypingConversion.delta_uses_original_value,
    ``GooseTypingConversion.zeta_uses_capture_avoiding_substitution,
    ``GooseTypingConversion.beta_uses_capture_avoiding_substitution,
    ``GooseTypingConversion.beta_substitution_preserves_scope,
    ``GooseTypingConversion.pi_prop_is_impredicative,
    ``GooseTypingConversion.pi_positive_is_max,
    ``GooseTypingConversion.zero_budget_refuses_inference,
    ``GooseTypingConversion.zero_budget_refuses_conversion,
    ``GooseTypingConversion.duplicate_precedes_semantics,
    ``GooseTypingConversion.refusal_preserves_all_bindings,
    ``GooseTypingConversion.success_stores_exact_fields,
    ``GooseTypingConversion.success_preserves_existing_prefix,
    ``GooseTypingConversion.validate_unknown_constant,
    ``GooseTypingConversion.unknown_zeta_value_is_not_erased,
    ``GooseTypingConversion.unknown_beta_argument_is_not_erased,
    ``GooseTypingConversion.run_has_no_authority,
    ``GooseTypingConversion.fatal_step_stops_suffix]
  for name in required do
    match env.find? name with
    | none => throwError "missing typing_conversion obligation: {name}"
    | some info =>
      unless info.isTheorem do
        throwError "typing_conversion obligation is not a theorem: {name}"
      let axioms ← collectAxioms name
      unless axioms.isEmpty do
        throwError "required typing/conversion theorem depends on axioms: {name}: {axioms}"
  let allowed : Array Name := #[``propext]
  let mut used : Array Name := #[]
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  for (name, info) in env.constants.toList do
    if (`GooseTypingConversion).isPrefixOf name then
      declarations := declarations + 1
      if info.isTheorem then theorems := theorems + 1
      let axioms ← collectAxioms name
      for axiomName in axioms do
        if !used.contains axiomName then used := used.push axiomName
        unless allowed.contains axiomName do
          throwError "typing_conversion namespace axiom audit rejected {name}: {axiomName}"
  logInfo m!"Typing/conversion axiom audit passed: {required.size} required theorems without axioms; {declarations} declarations; {theorems} theorem declarations; support axioms: {used}"

audit_goose_typing_conversion

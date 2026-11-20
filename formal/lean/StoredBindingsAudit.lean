import Lean.Elab.Command
import Lean.Util.CollectAxioms
import StoredBindings

open Lean Elab Command

/- Every required theorem and every declaration in the model namespace is
checked transitively. The required theorem closures must be axiom-free. -/
elab "audit_goose_stored_bindings" : command => do
  let env ← getEnv
  let required : Array Name := #[
    ``GooseStoredBindings.lookup_latest_binding,
    ``GooseStoredBindings.lookup_append_fresh_preserves_existing,
    ``GooseStoredBindings.fresh_good_payload_exact,
    ``GooseStoredBindings.fresh_alias_payload_exact,
    ``GooseStoredBindings.duplicate_precedes_checks,
    ``GooseStoredBindings.duplicate_preserves_environment,
    ``GooseStoredBindings.mismatch_preserves_environment,
    ``GooseStoredBindings.missing_alias_preserves_environment,
    ``GooseStoredBindings.wrong_type_alias_preserves_environment,
    ``GooseStoredBindings.initial_invariant,
    ``GooseStoredBindings.step_preserves_invariant,
    ``GooseStoredBindings.run_preserves_invariant,
    ``GooseStoredBindings.run_success_names_exact,
    ``GooseStoredBindings.run_environment_unique,
    ``GooseStoredBindings.run_success_count_exact,
    ``GooseStoredBindings.step_environment_extends,
    ``GooseStoredBindings.run_environment_extends,
    ``GooseStoredBindings.run_preserves_existing_binding,
    ``GooseStoredBindings.run_preserves_existing_binding_fields,
    ``GooseStoredBindings.step_preserves_existing_lookup,
    ``GooseStoredBindings.run_preserves_existing_lookup,
    ``GooseStoredBindings.run_preserves_name_uniqueness,
    ``GooseStoredBindings.halted_step_identity,
    ``GooseStoredBindings.halted_run_identity,
    ``GooseStoredBindings.halted_no_receipt,
    ``GooseStoredBindings.step_preserves_authority,
    ``GooseStoredBindings.run_preserves_authority,
    ``GooseStoredBindings.run_has_no_authority,
    ``GooseStoredBindings.completed_receipt_has_no_authority]
  for name in required do
    match env.find? name with
    | none => throwError "missing stored-binding obligation: {name}"
    | some info =>
      unless info.isTheorem do
        throwError "stored-binding obligation is not a theorem: {name}"
      let axioms ← collectAxioms name
      unless axioms.isEmpty do
        throwError "required stored-binding theorem depends on axioms: {name}: {axioms}"
  -- Generated structure injectivity support can use propext. No declared
  -- stored-binding theorem may depend on it, and no other axiom is permitted.
  let allowed : Array Name := #[``propext]
  let mut used : Array Name := #[]
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  for (name, info) in env.constants.toList do
    if (`GooseStoredBindings).isPrefixOf name then
      declarations := declarations + 1
      if info.isTheorem then theorems := theorems + 1
      let axioms ← collectAxioms name
      for axiomName in axioms do
        if !used.contains axiomName then used := used.push axiomName
        unless allowed.contains axiomName do
          throwError "stored-binding namespace axiom audit rejected {name}: {axiomName}"
  logInfo m!"Stored binding axiom audit passed: {required.size} required theorems without axioms; {declarations} declarations; {theorems} theorem declarations; support axioms: {used}"

audit_goose_stored_bindings

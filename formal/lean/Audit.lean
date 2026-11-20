import Lean.Elab.Command
import Lean.Util.CollectAxioms
import DefinitionTransactions

open Lean Elab Command

/- Every required theorem and every declaration in the model namespace is
checked transitively. The required theorem closures must be axiom-free. -/
elab "audit_goose_transactions" : command => do
  let env ← getEnv
  let required : Array Name := #[
    ``GooseTransactions.initial_invariant,
    ``GooseTransactions.step_preserves_invariant,
    ``GooseTransactions.run_preserves_invariant,
    ``GooseTransactions.run_environment_exact,
    ``GooseTransactions.run_environment_unique,
    ``GooseTransactions.run_success_count_exact,
    ``GooseTransactions.halted_step_identity,
    ``GooseTransactions.halted_run_identity,
    ``GooseTransactions.halted_no_receipt,
    ``GooseTransactions.duplicate_precedes_checks,
    ``GooseTransactions.duplicate_preserves_environment,
    ``GooseTransactions.mismatch_preserves_environment,
    ``GooseTransactions.missing_alias_preserves_environment,
    ``GooseTransactions.fresh_good_appends,
    ``GooseTransactions.fresh_scope_halts,
    ``GooseTransactions.mismatch_then_retry_succeeds,
    ``GooseTransactions.step_preserves_authority,
    ``GooseTransactions.run_preserves_authority,
    ``GooseTransactions.run_has_no_authority,
    ``GooseTransactions.completed_receipt_has_no_authority,
    ``GooseTransactions.run_environment_extends]
  for name in required do
    match env.find? name with
    | none => throwError "missing transaction obligation: {name}"
    | some info =>
      unless info.isTheorem do
        throwError "transaction obligation is not a theorem: {name}"
      let axioms ← collectAxioms name
      unless axioms.isEmpty do
        throwError "required transaction theorem depends on axioms: {name}: {axioms}"
  -- Generated structure injectivity support can use propext. No declared
  -- transaction theorem may depend on it, and no other axiom is permitted.
  let allowed : Array Name := #[``propext]
  let mut used : Array Name := #[]
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  for (name, info) in env.constants.toList do
    if (`GooseTransactions).isPrefixOf name then
      declarations := declarations + 1
      if info.isTheorem then theorems := theorems + 1
      let axioms ← collectAxioms name
      for axiomName in axioms do
        if !used.contains axiomName then used := used.push axiomName
        unless allowed.contains axiomName do
          throwError "transaction namespace axiom audit rejected {name}: {axiomName}"
  logInfo m!"Goose transaction axiom audit passed: {required.size} required theorems without axioms; {declarations} declarations; {theorems} theorem declarations; support axioms: {used}"

audit_goose_transactions

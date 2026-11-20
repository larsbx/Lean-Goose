import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Substitution

open Lean Elab Command

/- Audit every declaration in the new namespace, not just a sample. The named
obligations must have empty transitive axiom closures. Generated support alone
may use the explicitly allowed proposition-extensionality axiom. -/
elab "audit_goose_substitution" : command => do
  let env ← getEnv
  let required : Array Name := #[
    ``GooseSubstitution.lift_var_below,
    ``GooseSubstitution.lift_var_at_or_above,
    ``GooseSubstitution.lift_lambda,
    ``GooseSubstitution.lift_pi,
    ``GooseSubstitution.lift_let,
    ``GooseSubstitution.lift_zero,
    ``GooseSubstitution.lift_add,
    ``GooseSubstitution.lift_preserves_height,
    ``GooseSubstitution.lift_fixed_of_scoped,
    ``GooseSubstitution.lift_closed,
    ``GooseSubstitution.lift_scope,
    ``GooseSubstitution.lift_loose_bound,
    ``GooseSubstitution.substitute_var_below,
    ``GooseSubstitution.substitute_var_equal,
    ``GooseSubstitution.substitute_var_above,
    ``GooseSubstitution.substitute_lambda,
    ``GooseSubstitution.substitute_pi,
    ``GooseSubstitution.substitute_let,
    ``GooseSubstitution.substitute_fixed_of_scoped,
    ``GooseSubstitution.substitute_closed,
    ``GooseSubstitution.substitute_scope,
    ``GooseSubstitution.substitute_closed_top,
    ``GooseSubstitution.substitute_lift_one,
    ``GooseSubstitution.substitute_lift_one_top,
    ``GooseSubstitution.substitute_variable_after_lift,
    ``GooseSubstitution.lambda_substitution_avoids_capture,
    ``GooseSubstitution.pi_substitution_avoids_capture,
    ``GooseSubstitution.let_substitution_avoids_capture,
    ``GooseSubstitution.nested_lambda_substitution_avoids_capture,
    ``GooseSubstitution.nested_lambda_free_variable_stays_free,
    ``GooseSubstitution.refused_observation_is_empty,
    ``GooseSubstitution.observe_has_no_authority]
  for name in required do
    match env.find? name with
    | none => throwError "missing substitution obligation: {name}"
    | some info =>
      unless info.isTheorem do
        throwError "substitution obligation is not a theorem: {name}"
      let axioms ← collectAxioms name
      unless axioms.isEmpty do
        throwError "required substitution theorem depends on axioms: {name}: {axioms}"
  let allowed : Array Name := #[``propext]
  let mut used : Array Name := #[]
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  for (name, info) in env.constants.toList do
    if (`GooseSubstitution).isPrefixOf name then
      declarations := declarations + 1
      if info.isTheorem then theorems := theorems + 1
      let axioms ← collectAxioms name
      for axiomName in axioms do
        if !used.contains axiomName then used := used.push axiomName
        unless allowed.contains axiomName do
          throwError "substitution namespace axiom audit rejected {name}: {axiomName}"
  logInfo m!"Substitution axiom audit passed: {required.size} required theorems without axioms; {declarations} declarations; {theorems} theorem declarations; support axioms: {used}"

audit_goose_substitution

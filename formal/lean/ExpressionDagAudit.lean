import Lean.Elab.Command
import Lean.Util.CollectAxioms
import ExpressionDag

open Lean Elab Command

/- Audit every declaration in the new namespace, not just a sample. The named
obligations must have empty transitive axiom closures. Generated support alone
may use the explicitly allowed proposition-extensionality axiom. -/
elab "audit_goose_expression_dag" : command => do
  let env ← getEnv
  let required : Array Name := #[
    ``GooseExpressionDag.decodeNode_sound,
    ``GooseExpressionDag.decodeNode_complete,
    ``GooseExpressionDag.decodeNode_success_iff_topological,
    ``GooseExpressionDag.decode_sound,
    ``GooseExpressionDag.decode_complete,
    ``GooseExpressionDag.decode_length,
    ``GooseExpressionDag.decode_success_iff_topological,
    ``GooseExpressionDag.decode_rejects_non_topological,
    ``GooseExpressionDag.topological_edges_decrease,
    ``GooseExpressionDag.decoded_dag_has_no_cycles,
    ``GooseExpressionDag.decode_append,
    ``GooseExpressionDag.decode_prefix_extends,
    ``GooseExpressionDag.decode_preserves_old_node,
    ``GooseExpressionDag.decodeNode_append_preserves,
    ``GooseExpressionDag.shared_application_decodes,
    ``GooseExpressionDag.duplicated_children_decode_equally,
    ``GooseExpressionDag.duplicate_node_decodes_same,
    ``GooseExpressionDag.self_or_forward_reference_rejected,
    ``GooseExpressionDag.scoped_iff_loose,
    ``GooseExpressionDag.closed_iff_loose_zero,
    ``GooseExpressionDag.scoped_monotone,
    ``GooseExpressionDag.scopeCheck_correct,
    ``GooseExpressionDag.lambda_scope_distinguishes_domain_and_body,
    ``GooseExpressionDag.pi_scope_distinguishes_domain_and_body,
    ``GooseExpressionDag.let_scope_distinguishes_value_and_body,
    ``GooseExpressionDag.variable_requires_exact_depth,
    ``GooseExpressionDag.height_positive,
    ``GooseExpressionDag.child_height_lt,
    ``GooseExpressionDag.refused_observation_is_empty,
    ``GooseExpressionDag.observe_has_no_authority]
  for name in required do
    match env.find? name with
    | none => throwError "missing expression-DAG obligation: {name}"
    | some info =>
      unless info.isTheorem do
        throwError "expression-DAG obligation is not a theorem: {name}"
      let axioms ← collectAxioms name
      unless axioms.isEmpty do
        throwError "required expression-DAG theorem depends on axioms: {name}: {axioms}"
  let allowed : Array Name := #[``propext]
  let mut used : Array Name := #[]
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  for (name, info) in env.constants.toList do
    if (`GooseExpressionDag).isPrefixOf name then
      declarations := declarations + 1
      if info.isTheorem then theorems := theorems + 1
      let axioms ← collectAxioms name
      for axiomName in axioms do
        if !used.contains axiomName then used := used.push axiomName
        unless allowed.contains axiomName do
          throwError "expression-DAG namespace axiom audit rejected {name}: {axiomName}"
  logInfo m!"Expression DAG axiom audit passed: {required.size} required theorems without axioms; {declarations} declarations; {theorems} theorem declarations; support axioms: {used}"

audit_goose_expression_dag

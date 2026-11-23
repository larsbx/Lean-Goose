import SemanticEnvironment

namespace GooseEnvironmentScope
open GooseExpressionDag GooseSubstitution GooseTypingConversion GooseSemanticEnvironment

def LookupValuesClosed (environment : Environment) : Prop :=
  ∀ name binding, find environment name = some binding → Closed binding.value

def LookupValuesAvailable (environment : Environment) : Prop :=
  ∀ name binding, find environment name = some binding → Available environment binding.value

def LookupTypesScoped (environment : Environment) : Prop :=
  ∀ name binding, find environment name = some binding →
    Closed binding.ty ∧ Available environment binding.ty

theorem lookup_values_closed_of_certified {environment : Environment} (certified : Certified environment) :
    LookupValuesClosed environment :=
  fun name binding found => (certified_lookup_valid certified name binding found).valueClosed

theorem head_preserves_scope {environment : Environment} (values : LookupValuesClosed environment)
    {expression result : Expr} (reduction : HeadReduces environment expression result)
    {depth : Nat} (within : Scoped depth expression) : Scoped depth result := by
  induction reduction with
  | sort | var | lam | pi => exact within
  | delta found _ ih =>
    exact ih (scoped_monotone _ 0 depth (Nat.zero_le _) (values _ _ found))
  | zeta _ ih =>
    cases within with
    | letE _ value body => exact ih (substitute_scope _ _ depth 0 body value)
  | beta _ _ ihFn ihBody =>
    cases within with
    | app fn arg =>
      cases ihFn fn with
      | lam _ body => exact ihBody (substitute_scope _ _ depth 0 body arg)
  | app _ _ ih =>
    cases within with
    | app fn arg => exact .app (ih fn) arg

theorem normalization_preserves_scope {environment : Environment} (values : LookupValuesClosed environment)
    {expression result : Expr} (reduction : Normalizes environment expression result)
    {depth : Nat} (within : Scoped depth expression) : Scoped depth result := by
  induction reduction generalizing depth with
  | sort first | var first => exact head_preserves_scope values first within
  | app first _ _ ihA ihB =>
    cases head_preserves_scope values first within with
    | app a b => exact .app (ihA a) (ihB b)
  | lam first _ _ ihA ihB =>
    cases head_preserves_scope values first within with
    | lam a b => exact .lam (ihA a) (ihB b)
  | pi first _ _ ihA ihB =>
    cases head_preserves_scope values first within with
    | pi a b => exact .pi (ihA a) (ihB b)

private inductive HeadNormal : Expr → Prop where
  | sort (level) : HeadNormal (.sort level)
  | var (index) : HeadNormal (.var index)
  | lam (domain body) : HeadNormal (.lam domain body)
  | pi (domain body) : HeadNormal (.pi domain body)
  | app {fn arg} : HeadNormal fn → notLambda fn = true → HeadNormal (.app fn arg)

private theorem head_has_normal_result {environment : Environment} {expression result : Expr}
    (reduction : HeadReduces environment expression result) : HeadNormal result := by
  induction reduction with
  | sort => exact .sort _
  | var => exact .var _
  | lam => exact .lam _ _
  | pi => exact .pi _ _
  | delta _ _ ih | zeta _ ih | beta _ _ _ ih => exact ih
  | app _ neutral ih => exact .app ih neutral

private theorem head_normal_fixed {environment : Environment} {expression result : Expr}
    (canonical : HeadNormal expression) (reduction : HeadReduces environment expression result) :
    result = expression := by
  induction canonical generalizing result with
  | sort | var | lam | pi => cases reduction; rfl
  | app _ neutral ih =>
    cases reduction with
    | beta fn _ =>
      have same := ih fn
      rw [← same] at neutral
      cases neutral
    | app fn _ => rw [ih fn]

private theorem normalization_preserves_normal_head_kind {environment : Environment}
    {expression result : Expr} (canonical : HeadNormal expression)
    (reduction : Normalizes environment expression result) :
    notLambda result = notLambda expression := by
  cases reduction <;> rw [← head_normal_fixed canonical ‹HeadReduces _ _ _›] <;> rfl

/-- Full normal forms of the existing relation have no constants, lets, or beta redexes. -/
def NormalForm : Expr → Prop
  | .sort _ | .var _ => True
  | .const _ | .letE .. => False
  | .app fn arg => NormalForm fn ∧ NormalForm arg ∧ notLambda fn = true
  | .lam a b | .pi a b => NormalForm a ∧ NormalForm b

private theorem normalForm_headNormal {expression : Expr} (canonical : NormalForm expression) :
    HeadNormal expression := by
  induction expression with
  | sort => exact .sort _
  | var => exact .var _
  | lam => exact .lam _ _
  | pi => exact .pi _ _
  | const | letE => cases canonical
  | app fn arg ih _ => exact .app (ih canonical.1) canonical.2.2

theorem normalization_yields_normal_form {environment : Environment} {expression result : Expr}
    (reduction : Normalizes environment expression result) : NormalForm result := by
  induction reduction with
  | sort | var => trivial
  | lam _ _ _ a b | pi _ _ _ a b => exact ⟨a, b⟩
  | app first fn _ a b =>
    cases head_has_normal_result first with
    | app head neutral =>
      exact ⟨a, b, (normalization_preserves_normal_head_kind head fn).trans neutral⟩

theorem normalization_fixes_normal_form {environment : Environment} {expression result : Expr}
    (canonical : NormalForm expression) (reduction : Normalizes environment expression result) :
    result = expression := by
  induction reduction with
  | sort first | var first => exact head_normal_fixed (normalForm_headNormal canonical) first
  | @app input _ _ _ _ first _ _ ihA ihB =>
    have same := head_normal_fixed (normalForm_headNormal canonical) first
    subst input
    rw [ihA canonical.1, ihB canonical.2.1]
  | @lam input _ _ _ _ first _ _ ihA ihB | @pi input _ _ _ _ first _ _ ihA ihB =>
    have same := head_normal_fixed (normalForm_headNormal canonical) first
    subst input
    rw [ihA canonical.1, ihB canonical.2]

theorem normal_form_available (environment : Environment) {expression : Expr}
    (canonical : NormalForm expression) : Available environment expression := by
  induction expression with
  | sort | var => trivial
  | const | letE => cases canonical
  | app fn arg ihFn ihArg => exact ⟨ihFn canonical.1, ihArg canonical.2.1⟩
  | lam a b ihA ihB | pi a b ihA ihB => exact ⟨ihA canonical.1, ihB canonical.2⟩

theorem converted_normal_form_preserves_scope {environment : Environment} {stored declared : Expr}
    {depth : Nat} (values : LookupValuesClosed environment) (canonical : NormalForm stored)
    (conversion : Converts environment stored declared) (within : Scoped depth declared) :
    Scoped depth stored := by
  obtain ⟨_, storedReduction, declaredReduction⟩ := conversion
  have same := normalization_fixes_normal_form canonical storedReduction
  exact same ▸ normalization_preserves_scope values declaredReduction within

theorem binding_valid_inferred_closed_available {environment : Environment} {binding : Binding}
    (values : LookupValuesClosed environment) (valid : BindingValidIn environment binding) :
    Closed binding.inferred ∧ Available environment binding.inferred := by
  obtain ⟨_, _, normalized⟩ := valid.valueDerivation
  have canonical := normalization_yields_normal_form normalized
  exact ⟨converted_normal_form_preserves_scope values canonical valid.conversion valid.typeClosed,
    normal_form_available environment canonical⟩

theorem checked_success_inferred_scope_of_closed_values (fuel : Nat) (environment : Environment)
    (definition : Definition) (stored : Expr) (values : LookupValuesClosed environment)
    (success : checked fuel environment definition = .ok stored) :
    Closed stored ∧ Available environment stored :=
  binding_valid_inferred_closed_available values
    (checked_success_certifies_binding fuel environment definition stored success)

theorem checked_success_inferred_closed_available (fuel : Nat) (environment : Environment)
    (definition : Definition) (stored : Expr) (certified : Certified environment)
    (success : checked fuel environment definition = .ok stored) :
    Closed stored ∧ Available environment stored :=
  checked_success_inferred_scope_of_closed_values fuel environment definition stored
    (lookup_values_closed_of_certified certified) success

def ScopedAvailable (environment : Environment) (depth : Nat) (expression : Expr) : Prop :=
  Scoped depth expression ∧ Available environment expression

/-- Context entries are stored innermost first, relative to the outer tail. -/
inductive ContextScoped (environment : Environment) : Context → Prop where
  | empty : ContextScoped environment []
  | cons {outer type} : ContextScoped environment outer →
      ScopedAvailable environment outer.length type → ContextScoped environment (type :: outer)

inductive ContextValid (environment : Environment) : Context → Prop where
  | empty : ContextValid environment []
  | cons {outer type level} : ContextValid environment outer →
      ScopedAvailable environment outer.length type → HasSort environment outer type level →
      ContextValid environment (type :: outer)

theorem ContextValid.scoped {environment : Environment} {context : Context}
    (valid : ContextValid environment context) : ContextScoped environment context := by
  induction valid with
  | empty => exact .empty
  | cons _ within _ ih => exact .cons ih within

theorem lift_preserves_available {environment : Environment} {expression : Expr}
    (available : Available environment expression) (amount cutoff : Nat) :
    Available environment (lift amount cutoff expression) := by
  induction expression generalizing cutoff with
  | sort => trivial
  | var index =>
    by_cases below : index < cutoff
    · rw [lift_var_below _ _ _ below]; trivial
    · rw [lift_var_at_or_above _ _ _ (Nat.le_of_not_gt below)]; trivial
  | const => exact available
  | app _ _ a b => exact ⟨a available.1 cutoff, b available.2 cutoff⟩
  | lam _ _ a b | pi _ _ a b => exact ⟨a available.1 cutoff, b available.2 (cutoff + 1)⟩
  | letE _ _ _ a b c => exact ⟨a available.1 cutoff, b available.2.1 cutoff, c available.2.2 (cutoff + 1)⟩

theorem substitution_preserves_available {environment : Environment} {expression replacement : Expr}
    (available : Available environment expression) (inserted : Available environment replacement) (cutoff : Nat) :
    Available environment (substitute replacement cutoff expression) := by
  induction expression generalizing cutoff with
  | sort => trivial
  | var index =>
    by_cases below : index < cutoff
    · rw [substitute_var_below _ _ _ below]; trivial
    · by_cases equal : index = cutoff
      · rw [equal, substitute_var_equal]; exact lift_preserves_available inserted cutoff 0
      · rw [substitute_var_above _ _ _ (Nat.lt_of_le_of_ne (Nat.le_of_not_gt below) (Ne.symm equal))]; trivial
  | const => exact available
  | app _ _ a b => exact ⟨a available.1 cutoff, b available.2 cutoff⟩
  | lam _ _ a b | pi _ _ a b => exact ⟨a available.1 cutoff, b available.2 (cutoff + 1)⟩
  | letE _ _ _ a b c => exact ⟨a available.1 cutoff, b available.2.1 cutoff, c available.2.2 (cutoff + 1)⟩

theorem head_preserves_available {environment : Environment} (values : LookupValuesAvailable environment)
    {expression result : Expr} (reduction : HeadReduces environment expression result)
    (available : Available environment expression) : Available environment result := by
  induction reduction with
  | sort | var | lam | pi => exact available
  | delta found _ ih => exact ih (values _ _ found)
  | zeta _ ih => exact ih (substitution_preserves_available available.2.2 available.2.1 0)
  | beta _ _ ihFn ihBody =>
    exact ihBody (substitution_preserves_available (ihFn available.1).2 available.2 0)
  | app _ _ ih => exact ⟨ih available.1, available.2⟩

private theorem context_lookup_outer {environment : Environment} {context : Context}
    (contextScoped : ContextScoped environment context) {index : Nat} {type : Expr}
    (found : lookup context index = some type) :
    ∃ depth, context.length = depth + (index + 1) ∧ ScopedAvailable environment depth type := by
  induction contextScoped generalizing index with
  | empty => cases found
  | @cons outer entry _ within ih =>
    cases index with
    | zero =>
      change some entry = some type at found
      cases found
      exact ⟨outer.length, rfl, within⟩
    | succ index =>
      obtain ⟨depth, length, valid⟩ := ih (index := index) found
      exact ⟨depth, congrArg Nat.succ length, valid⟩

theorem scoped_context_lifts_lookup {environment : Environment} {context : Context}
    (contextScoped : ContextScoped environment context) {index : Nat} {type : Expr}
    (found : lookup context index = some type) :
    ScopedAvailable environment context.length (lift (index + 1) 0 type) := by
  obtain ⟨depth, length, within, available⟩ := context_lookup_outer contextScoped found
  rw [length]
  exact ⟨lift_scope _ depth (index + 1) 0 within, lift_preserves_available available (index + 1) 0⟩

/-- Structural inference uses old declared types, old delta values, and the
    shape of the context. It does not require a sort derivation for every entry. -/
theorem inference_preserves_scope_available {environment : Environment}
    (types : LookupTypesScoped environment) (closedValues : LookupValuesClosed environment)
    (availableValues : LookupValuesAvailable environment)
    {context : Context} {expression type : Expr} (inference : Infers environment context expression type) :
    ContextScoped environment context → ScopedAvailable environment context.length expression →
    ScopedAvailable environment context.length type := by
  induction inference using Infers.rec (motive_2 := fun _ _ _ _ => True) with
  | sort | pi => exact fun _ _ => ⟨.sort _ _, True.intro⟩
  | var found => exact fun within _ => scoped_context_lifts_lookup within found
  | const found =>
    intro _ _
    obtain ⟨within, available⟩ := types _ _ found
    exact ⟨scoped_monotone _ 0 _ (Nat.zero_le _) within, available⟩
  | lam _ _ _ ih =>
    intro contextScoped input
    obtain ⟨scope, available⟩ := input
    cases scope with
    | lam domain body =>
      obtain ⟨bodyScope, bodyAvailable⟩ := ih (.cons contextScoped ⟨domain, available.1⟩) ⟨body, available.2⟩
      exact ⟨.pi domain bodyScope, ⟨available.1, bodyAvailable⟩⟩
  | app _ reduced _ _ ih _ =>
    intro contextScoped input
    obtain ⟨scope, available⟩ := input
    cases scope with
    | app fn arg =>
      obtain ⟨fnScope, fnAvailable⟩ := ih contextScoped ⟨fn, available.1⟩
      have piAvailable := head_preserves_available availableValues reduced fnAvailable
      cases head_preserves_scope closedValues reduced fnScope with
      | pi _ codomain =>
        exact ⟨substitute_scope _ _ _ 0 codomain arg,
          substitution_preserves_available piAvailable.2 available.2 0⟩
  | letE _ _ _ _ _ _ ih =>
    intro contextScoped input
    obtain ⟨scope, available⟩ := input
    cases scope with
    | letE _ value body =>
      exact ih contextScoped ⟨substitute_scope _ _ _ 0 body value,
        substitution_preserves_available available.2.2 available.2.1 0⟩
  | intro => trivial

theorem valid_context_inference_scope {environment : Environment} {context : Context}
    {expression type : Expr} (certified : Certified environment) (valid : ContextValid environment context)
    (inference : Infers environment context expression type)
    (input : ScopedAvailable environment context.length expression) :
    ScopedAvailable environment context.length type := by
  apply inference_preserves_scope_available _ (lookup_values_closed_of_certified certified) _ inference
    valid.scoped input
  · intro name binding found
    have bindingValid := certified_lookup_valid certified name binding found
    exact ⟨bindingValid.typeClosed, bindingValid.typeAvailable⟩
  · exact fun name binding found => (certified_lookup_valid certified name binding found).valueAvailable

/-- All three fields of a binding, including its normal inferred field, are
    scoped and available against the current environment. -/
theorem certified_lookup_all_fields {environment : Environment} {name : List Nat} {binding : Binding}
    (certified : Certified environment) (found : find environment name = some binding) :
    ScopedAvailable environment 0 binding.ty ∧ ScopedAvailable environment 0 binding.value ∧
      ScopedAvailable environment 0 binding.inferred := by
  have valid := certified_lookup_valid certified name binding found
  exact ⟨⟨valid.typeClosed, valid.typeAvailable⟩, ⟨valid.valueClosed, valid.valueAvailable⟩,
    binding_valid_inferred_closed_available (lookup_values_closed_of_certified certified) valid⟩

private theorem member_append_singleton {α : Type} {entry last : α} (entries : List α)
    (member : entry ∈ entries ++ [last]) : entry ∈ entries ∨ entry = last := by
  induction entries with
  | nil =>
    change entry ∈ [last] at member
    cases member with
    | head => exact .inr rfl
    | tail _ impossible => cases impossible
  | cons first rest ih =>
    change entry ∈ first :: (rest ++ [last]) at member
    cases member with
    | head => exact .inl (.head _)
    | tail _ later =>
      cases ih later with
      | inl earlier => exact .inl (.tail _ earlier)
      | inr equal => exact .inr equal

theorem certified_record_lookup {environment : Environment} {binding : Binding}
    (certified : Certified environment) (member : binding ∈ environment) :
    find environment binding.name = some binding := by
  induction certified with
  | empty => cases member
  | @append before newest _ fresh _ ih =>
    cases member_append_singleton before member with
    | inl earlier => exact fresh_append_extends before newest fresh _ _ (ih earlier)
    | inr same =>
      subst binding
      exact find_latest before newest

private theorem snapshot_certified {snapshots : List Step} {snapshot : Step}
    (certified : SnapshotsCertified snapshots) (member : snapshot ∈ snapshots) :
    Certified snapshot.environment := by
  induction snapshots with
  | nil => cases member
  | cons first rest ih =>
    cases member with
    | head => exact certified.1
    | tail _ later => exact ih certified.2 later

theorem run_snapshots_all_fields (fuel : Nat) (environment : Environment) (definitions : List Definition)
    (certified : Certified environment) {snapshot : Step} {binding : Binding}
    (processed : snapshot ∈ (runFrom fuel environment definitions).steps)
    (member : binding ∈ snapshot.environment) :
    ScopedAvailable snapshot.environment 0 binding.ty ∧
      ScopedAvailable snapshot.environment 0 binding.value ∧
      ScopedAvailable snapshot.environment 0 binding.inferred :=
  have current := snapshot_certified (run_snapshots_certified fuel environment definitions certified) processed
  certified_lookup_all_fields current (certified_record_lookup current member)

theorem run_final_environment_all_fields (fuel : Nat) (environment : Environment) (definitions : List Definition)
    (certified : Certified environment) {binding : Binding}
    (member : binding ∈ finalEnvironment environment (runFrom fuel environment definitions).steps) :
    let final := finalEnvironment environment (runFrom fuel environment definitions).steps
    ScopedAvailable final 0 binding.ty ∧ ScopedAvailable final 0 binding.value ∧ ScopedAvailable final 0 binding.inferred :=
  have current := run_final_environment_certified fuel environment definitions certified
  certified_lookup_all_fields current (certified_record_lookup current member)

/- Concrete controls. The forged environment exists only at the model boundary. -/
private def forgedDelta : Environment :=
  [⟨[65], .sort 1, .var 0, .sort 1⟩]

private def aliasIdentity : Definition :=
  ⟨[105, 100], .pi (.const [65]) (.const [65]), .lam (.const [65]) (.var 0)⟩

theorem malformed_delta_value_escapes :
    checked 16 forgedDelta aliasIdentity = .ok (.pi (.var 0) (.var 0)) ∧
      ¬ Closed (.pi (.var 0) (.var 0)) ∧ ¬ LookupValuesClosed forgedDelta := by
  refine ⟨rfl, ?_, ?_⟩
  · intro closed
    cases closed with
    | pi outer _ => cases outer with
      | var bound => exact Nat.not_lt_zero _ bound
  · intro safe
    have within := safe [65] ⟨[65], .sort 1, .var 0, .sort 1⟩ rfl
    cases within with
    | var bound => exact Nat.not_lt_zero _ bound

private def forgedType : Environment :=
  [⟨[65], .letE (.sort 2) (.var 0) (.sort 1), .sort 0, .var 0⟩]

theorem closed_delta_values_allow_scope_of_normalized_field :
    LookupValuesClosed forgedType ∧
    ¬ Scoped 0 (.letE (.sort 2) (.var 0) (.sort 1)) ∧
    checked 16 forgedType ⟨[66], .sort 1, .const [65]⟩ = .ok (.sort 1) := by
  refine ⟨?_, ?_, rfl⟩
  · intro name binding found
    change (if ([65] : List Nat) = name
      then some ⟨[65], .letE (.sort 2) (.var 0) (.sort 1), .sort 0, .var 0⟩
      else none) = some binding at found
    by_cases same : ([65] : List Nat) = name
    · rw [ite_eq_left same] at found
      cases found
      exact .sort _ _
    · rw [ite_eq_right same] at found
      cases found
  · intro scope
    cases scope with
    | letE _ value _ => cases value with
      | var bound => exact Nat.not_lt_zero _ bound

theorem dependent_context_valid_and_lifts :
    ContextValid [] [.var 0, .sort 1] ∧
    infer 16 [] [.var 0, .sort 1] (.var 0) = .ok (.var 1) := by
  exact ⟨.cons (.cons .empty ⟨.sort _ _, True.intro⟩ (.intro (.sort [] 1) (.sort 2)))
    ⟨.var (Nat.zero_lt_succ _), True.intro⟩ (.intro (.var rfl) (.sort 1)), rfl⟩

theorem self_scoped_context_refused :
    ¬ ContextScoped [] [.var 0] ∧
    infer 16 [] [.var 0] (.var 0) = .ok (.var 1) ∧ ¬ Scoped 1 (.var 1) := by
  refine ⟨?_, rfl, ?_⟩
  · intro contextScope
    cases contextScope with
    | cons _ within => cases within.1 with
      | var bound => exact Nat.not_lt_zero _ bound
  · intro scope
    cases scope with
    | var bound => exact Nat.lt_irrefl _ bound

theorem scoped_context_can_lack_sort :
    ContextScoped [] [.lam (.sort 1) (.var 0)] ∧
    ¬ ContextValid [] [.lam (.sort 1) (.var 0)] := by
  refine ⟨.cons .empty ⟨.lam (.sort _ _) (.var (Nat.zero_lt_succ _)), ⟨True.intro, True.intro⟩⟩, ?_⟩
  intro valid
  cases valid with
  | cons _ _ sort =>
    cases sort with
    | intro infer reduced =>
      cases infer
      cases reduced

private def universeAlias : Definition := ⟨[85], .sort 2, .sort 1⟩

theorem conversion_refusal_does_not_insert :
    let environment := insert [] universeAlias (.sort 2)
    let candidate : Definition := ⟨[86], .sort 3, .const [85]⟩
    Certified environment ∧ checked 16 environment candidate = .error 6 ∧
      (step 16 environment candidate).environment = environment ∧
      find (step 16 environment candidate).environment candidate.name = none := by
  exact ⟨successful_insertion_certified 16 [] universeAlias (.sort 2) .empty rfl, rfl, rfl, rfl⟩

end GooseEnvironmentScope

import TypingConversion
import StoredBindings

/-!
Semantic environments for the numeric-sort reference fragment.

Certificates use independent typing/reduction judgments in the actual predecessor
environment, rather than successful-check equations. Lookup-preserving extension
transports those judgments to later environments. The bridge to the earlier
stored-binding scope preserves all three structural payloads and assumes an
injective coding of names; it does not equate the earlier four-action checker
with the compound-expression checker. Context well-formedness, typed subject
reduction, totality, and universal native refinement remain separate obligations.
-/
namespace GooseSemanticEnvironment
open GooseExpressionDag GooseTypingConversion

/-- Every syntactically occurring constant already has a stored binding. -/
def Available (environment : Environment) : Expr → Prop
  | .sort _ | .var _ => True
  | .const name => ∃ binding, find environment name = some binding
  | .app a b | .lam a b | .pi a b => Available environment a ∧ Available environment b
  | .letE a b c => Available environment a ∧ Available environment b ∧ Available environment c

/-- Preserve the complete selected binding, including type/value/inferred. -/
def LookupExtends (before after : Environment) : Prop :=
  ∀ name binding, find before name = some binding → find after name = some binding

structure BindingValidIn (environment : Environment) (binding : Binding) : Prop where
  typeClosed : Closed binding.ty
  valueClosed : Closed binding.value
  typeAvailable : Available environment binding.ty
  valueAvailable : Available environment binding.value
  declaredSort : ∃ level, HasSort environment [] binding.ty level
  valueDerivation : ∃ actual, Infers environment [] binding.value actual ∧
    Normalizes environment actual binding.inferred
  conversion : Converts environment binding.inferred binding.ty

/-- Each entry is justified against precisely the prefix preceding insertion. -/
inductive Certified : Environment → Prop where
  | empty : Certified []
  | append {environment binding} : Certified environment →
      find environment binding.name = none → BindingValidIn environment binding →
      Certified (environment ++ [binding])

def SnapshotsCertified : List Step → Prop
  | [] => True
  | snapshot :: rest => Certified snapshot.environment ∧ SnapshotsCertified rest

def finalEnvironment (initial : Environment) : List Step → Environment
  | [] => initial
  | snapshot :: rest => finalEnvironment snapshot.environment rest

def projectBinding (nameCode : List Nat → Nat) (binding : Binding) : GooseStoredBindings.Binding :=
  ⟨nameCode binding.name, encode binding.ty, encode binding.value, encode binding.inferred⟩

def projectEnvironment (nameCode : List Nat → Nat) (environment : Environment) :
    List GooseStoredBindings.Binding := environment.map (projectBinding nameCode)

theorem validate_implies_available (environment : Environment) (expression : Expr)
    (valid : validate environment expression = .ok ()) : Available environment expression := by
  induction expression with
  | sort => trivial
  | var => trivial
  | const name =>
    cases found : find environment name with
    | none => simp only [validate, found] at valid; cases valid
    | some binding => exact ⟨binding, found⟩
  | app a b iha ihb | lam a b iha ihb | pi a b iha ihb =>
    cases first : validate environment a with
    | error code => simp only [validate, first, bind, Except.bind] at valid; cases valid
    | ok token =>
      cases token
      simp only [validate, first, bind, Except.bind] at valid
      exact ⟨iha first, ihb valid⟩
  | letE a b c iha ihb ihc =>
    cases first : validate environment a with
    | error code => simp only [validate, first, bind, Except.bind] at valid; cases valid
    | ok token =>
      cases token
      cases second : validate environment b with
      | error code => simp only [validate, first, second, bind, Except.bind] at valid; cases valid
      | ok token =>
        cases token
        simp only [validate, first, second, bind, Except.bind] at valid
        exact ⟨iha first, ihb second, ihc valid⟩

theorem available_monotone (before after : Environment) (extension : LookupExtends before after)
    (expression : Expr) (available : Available before expression) : Available after expression := by
  induction expression with
  | sort => trivial
  | var => trivial
  | const name =>
    obtain ⟨binding, found⟩ := available
    exact ⟨binding, extension name binding found⟩
  | app a b iha ihb | lam a b iha ihb | pi a b iha ihb => exact ⟨iha available.1, ihb available.2⟩
  | letE a b c iha ihb ihc => exact ⟨iha available.1, ihb available.2.1, ihc available.2.2⟩

theorem lookup_extends_reflexive (environment : Environment) : LookupExtends environment environment :=
  fun _ _ found => found

theorem lookup_extends_transitive (a b c : Environment)
    (ab : LookupExtends a b) (bc : LookupExtends b c) : LookupExtends a c :=
  fun name binding found => bc name binding (ab name binding found)

theorem find_snoc (environment : Environment) (binding : Binding) (name : List Nat) :
    find (environment ++ [binding]) name =
      if binding.name = name then some binding else find environment name := by
  induction environment with
  | nil => rfl
  | cons first rest ih =>
    change (match find (rest ++ [binding]) name with
      | some found => some found
      | none => if first.name = name then some first else none) = _
    rw [ih]
    by_cases equal : binding.name = name
    · rw [ite_eq_left equal, ite_eq_left equal]
    · rw [ite_eq_right equal, ite_eq_right equal]
      rfl

theorem fresh_append_extends (environment : Environment) (binding : Binding)
    (fresh : find environment binding.name = none) : LookupExtends environment (environment ++ [binding]) := by
  intro name previous found
  have different : binding.name ≠ name := by
    intro equal
    rw [equal, found] at fresh
    cases fresh
  rw [find_snoc, ite_eq_right different]
  exact found

theorem find_latest (environment : Environment) (binding : Binding) :
    find (environment ++ [binding]) binding.name = some binding := by
  rw [find_snoc, ite_eq_left rfl]

theorem head_reduction_weaken {before after : Environment} (extension : LookupExtends before after)
    {expression result : Expr} (derivation : HeadReduces before expression result) :
    HeadReduces after expression result := by
  induction derivation with
  | sort level => exact .sort level
  | var index => exact .var index
  | lam domain body => exact .lam domain body
  | pi domain body => exact .pi domain body
  | delta found reduced ih => exact .delta (extension _ _ found) ih
  | zeta reduced ih => exact .zeta ih
  | beta first second ihFirst ihSecond => exact .beta ihFirst ihSecond
  | app first neutral ih => exact .app ih neutral

theorem normalization_weaken {before after : Environment} (extension : LookupExtends before after)
    {expression result : Expr} (derivation : Normalizes before expression result) :
    Normalizes after expression result := by
  induction derivation with
  | sort first => exact .sort (head_reduction_weaken extension first)
  | var first => exact .var (head_reduction_weaken extension first)
  | app first a b iha ihb => exact .app (head_reduction_weaken extension first) iha ihb
  | lam first a b iha ihb => exact .lam (head_reduction_weaken extension first) iha ihb
  | pi first a b iha ihb => exact .pi (head_reduction_weaken extension first) iha ihb

theorem conversion_weaken {before after : Environment} (extension : LookupExtends before after)
    {left right : Expr} (conversion : Converts before left right) : Converts after left right := by
  obtain ⟨result, first, second⟩ := conversion
  exact ⟨result, normalization_weaken extension first, normalization_weaken extension second⟩

theorem inference_weaken {before after : Environment} (extension : LookupExtends before after)
    {context : Context} {expression type : Expr} (derivation : Infers before context expression type) :
    Infers after context expression type := by
  induction derivation using Infers.rec
      (motive_2 := fun context expression level _ => HasSort after context expression level) with
  | sort context level => exact .sort context level
  | var found => exact .var found
  | const found => exact .const (extension _ _ found)
  | lam domain body ihDomain ihBody => exact .lam ihDomain ihBody
  | pi domain codomain ihDomain ihCodomain => exact .pi ihDomain ihCodomain
  | app fn reduced arg conversion ihFn ihArg =>
    exact .app ihFn (head_reduction_weaken extension reduced) ihArg (conversion_weaken extension conversion)
  | letE type value conversion result ihType ihValue ihResult =>
    exact .letE ihType ihValue (conversion_weaken extension conversion) ihResult
  | intro type reduced ihType => exact .intro ihType (head_reduction_weaken extension reduced)

theorem sort_weaken {before after : Environment} (extension : LookupExtends before after)
    {context : Context} {expression : Expr} {level : Nat}
    (derivation : HasSort before context expression level) : HasSort after context expression level := by
  cases derivation with
  | intro type reduced => exact .intro (inference_weaken extension type) (head_reduction_weaken extension reduced)

theorem binding_valid_weaken {before after : Environment} (extension : LookupExtends before after)
    {binding : Binding} (valid : BindingValidIn before binding) : BindingValidIn after binding := by
  obtain ⟨level, sort⟩ := valid.declaredSort
  obtain ⟨actual, typing, normalized⟩ := valid.valueDerivation
  exact ⟨valid.typeClosed, valid.valueClosed,
    available_monotone before after extension binding.ty valid.typeAvailable,
    available_monotone before after extension binding.value valid.valueAvailable,
    ⟨level, sort_weaken extension sort⟩,
    ⟨actual, inference_weaken extension typing, normalization_weaken extension normalized⟩,
    conversion_weaken extension valid.conversion⟩

theorem checked_success_preconditions (fuel : Nat) (environment : Environment) (definition : Definition)
    (stored : Expr) (success : checked fuel environment definition = .ok stored) :
    find environment definition.name = none ∧ Closed definition.ty ∧ Closed definition.value ∧
    Available environment definition.ty ∧ Available environment definition.value := by
  cases found : find environment definition.name with
  | some binding => simp only [checked, found] at success; cases success
  | none =>
    cases scope : scopeCheck definition.ty 0 && scopeCheck definition.value 0 with
    | false => simp only [checked, found, scope] at success; cases success
    | true =>
      cases typeValid : validate environment definition.ty with
      | error code => simp only [checked, found, scope, typeValid, bind, Except.bind] at success; cases success
      | ok token =>
        cases token
        cases valueValid : validate environment definition.value with
        | error code => simp only [checked, found, scope, typeValid, valueValid, bind, Except.bind] at success; cases success
        | ok token =>
          cases token
          have scopes : scopeCheck definition.ty 0 = true ∧ scopeCheck definition.value 0 = true := by
            cases left : scopeCheck definition.ty 0 with
            | false => rw [left] at scope; cases scope
            | true =>
              cases right : scopeCheck definition.value 0 with
              | false => rw [left, right] at scope; cases scope
              | true => exact ⟨rfl, rfl⟩
          exact ⟨rfl, (scopeCheck_correct definition.ty 0).1 scopes.1,
            (scopeCheck_correct definition.value 0).1 scopes.2,
            validate_implies_available environment definition.ty typeValid,
            validate_implies_available environment definition.value valueValid⟩

theorem checked_success_certifies_binding (fuel : Nat) (environment : Environment) (definition : Definition)
    (stored : Expr) (success : checked fuel environment definition = .ok stored) :
    BindingValidIn environment ⟨definition.name, definition.ty, definition.value, stored⟩ := by
  have pre := checked_success_preconditions fuel environment definition stored success
  have semantic := checkValue_sound fuel environment definition stored
    (checked_success_has_semantics fuel environment definition stored success)
  exact ⟨pre.2.1, pre.2.2.1, pre.2.2.2.1, pre.2.2.2.2,
    semantic.1, semantic.2.1, semantic.2.2⟩

theorem successful_insertion_certified (fuel : Nat) (environment : Environment) (definition : Definition)
    (stored : Expr) (certified : Certified environment)
    (success : checked fuel environment definition = .ok stored) :
    Certified (insert environment definition stored) :=
  .append certified (checked_success_preconditions fuel environment definition stored success).1
    (checked_success_certifies_binding fuel environment definition stored success)

theorem refusal_retains_certificate (fuel : Nat) (environment : Environment) (definition : Definition)
    (code : Nat) (certified : Certified environment)
    (refusal : checked fuel environment definition = .error code) :
    Certified (step fuel environment definition).environment := by
  rw [refusal_preserves_all_bindings fuel environment definition code refusal]
  exact certified

theorem step_preserves_certification (fuel : Nat) (environment : Environment) (definition : Definition)
    (certified : Certified environment) : Certified (step fuel environment definition).environment := by
  cases result : checked fuel environment definition with
  | error code => exact refusal_retains_certificate fuel environment definition code certified result
  | ok stored =>
    rw [success_stores_exact_fields fuel environment definition stored result]
    exact successful_insertion_certified fuel environment definition stored certified result

theorem step_preserves_lookup (fuel : Nat) (environment : Environment) (definition : Definition) :
    LookupExtends environment (step fuel environment definition).environment := by
  cases result : checked fuel environment definition with
  | error code =>
    rw [refusal_preserves_all_bindings fuel environment definition code result]
    exact lookup_extends_reflexive environment
  | ok stored =>
    rw [success_stores_exact_fields fuel environment definition stored result]
    exact fresh_append_extends environment ⟨definition.name, definition.ty, definition.value, stored⟩
      (checked_success_preconditions fuel environment definition stored result).1

theorem certified_lookup_valid {environment : Environment} (certified : Certified environment)
    (name : List Nat) (binding : Binding) (found : find environment name = some binding) :
    BindingValidIn environment binding := by
  induction certified with
  | empty => cases found
  | @append previous newest prior fresh valid ih =>
    have extension := fresh_append_extends previous newest fresh
    rw [find_snoc] at found
    by_cases same : newest.name = name
    · rw [ite_eq_left same] at found
      cases found
      exact binding_valid_weaken extension valid
    · rw [ite_eq_right same] at found
      exact binding_valid_weaken extension (ih found)

theorem certified_lookup_has_closed_originals {environment : Environment} (certified : Certified environment)
    (name : List Nat) (binding : Binding) (found : find environment name = some binding) :
    Closed binding.ty ∧ Closed binding.value := by
  have valid := certified_lookup_valid certified name binding found
  exact ⟨valid.typeClosed, valid.valueClosed⟩

theorem certified_lookup_conversion {environment : Environment} (certified : Certified environment)
    (name : List Nat) (binding : Binding) (found : find environment name = some binding) :
    Converts environment binding.inferred binding.ty :=
  (certified_lookup_valid certified name binding found).conversion

theorem run_snapshots_certified (fuel : Nat) (environment : Environment) (definitions : List Definition)
    (certified : Certified environment) : SnapshotsCertified (runFrom fuel environment definitions).steps := by
  induction definitions generalizing environment with
  | nil => trivial
  | cons definition rest ih =>
    have next := step_preserves_certification fuel environment definition certified
    unfold runFrom
    dsimp only
    cases stops : fatal (step fuel environment definition).outcome with
    | true => exact ⟨next, True.intro⟩
    | false => exact ⟨next, ih _ next⟩

theorem certified_snapshots_end (environment : Environment) (steps : List Step)
    (initial : Certified environment) (snapshots : SnapshotsCertified steps) :
    Certified (finalEnvironment environment steps) := by
  induction steps generalizing environment with
  | nil => exact initial
  | cons snapshot rest ih => exact ih snapshot.environment snapshots.1 snapshots.2

theorem run_final_environment_certified (fuel : Nat) (environment : Environment) (definitions : List Definition)
    (certified : Certified environment) : Certified (finalEnvironment environment (runFrom fuel environment definitions).steps) :=
  certified_snapshots_end environment _ certified (run_snapshots_certified fuel environment definitions certified)

theorem empty_run_has_semantic_environment (fuel : Nat) (definitions : List Definition) :
    Certified (finalEnvironment [] (observe fuel definitions).steps) :=
  run_final_environment_certified fuel [] definitions .empty

theorem run_preserves_lookup (fuel : Nat) (environment : Environment) (definitions : List Definition) :
    LookupExtends environment (finalEnvironment environment (runFrom fuel environment definitions).steps) := by
  induction definitions generalizing environment with
  | nil => exact lookup_extends_reflexive environment
  | cons definition rest ih =>
    have next := step_preserves_lookup fuel environment definition
    unfold runFrom
    dsimp only
    cases stops : fatal (step fuel environment definition).outcome with
    | true => exact next
    | false => exact lookup_extends_transitive environment _ _ next (ih _)

theorem run_preserves_semantic_judgments (fuel : Nat) (environment : Environment) (definitions : List Definition)
    (binding : Binding) (valid : BindingValidIn environment binding) :
    BindingValidIn (finalEnvironment environment (runFrom fuel environment definitions).steps) binding :=
  binding_valid_weaken (run_preserves_lookup fuel environment definitions) valid

theorem step_environment_prefix (fuel : Nat) (environment : Environment) (definition : Definition) :
    ∃ suffix, (step fuel environment definition).environment = environment ++ suffix := by
  cases result : checked fuel environment definition with
  | error code =>
    refine ⟨[], ?_⟩
    rw [refusal_preserves_all_bindings fuel environment definition code result]
    exact (append_nil_exact environment).symm
  | ok stored => exact success_preserves_existing_prefix fuel environment definition stored result

theorem run_environment_prefix (fuel : Nat) (environment : Environment) (definitions : List Definition) :
    ∃ suffix, finalEnvironment environment (runFrom fuel environment definitions).steps = environment ++ suffix := by
  induction definitions generalizing environment with
  | nil => exact ⟨[], (append_nil_exact environment).symm⟩
  | cons definition rest ih =>
    obtain ⟨first, stepEqual⟩ := step_environment_prefix fuel environment definition
    cases stops : fatal (step fuel environment definition).outcome with
    | true =>
      refine ⟨first, ?_⟩
      unfold runFrom
      dsimp only
      rw [stops]
      exact stepEqual
    | false =>
      obtain ⟨remaining, finalEqual⟩ := ih (step fuel environment definition).environment
      refine ⟨first ++ remaining, ?_⟩
      unfold runFrom
      dsimp only
      rw [stops]
      change finalEnvironment (step fuel environment definition).environment
        (runFrom fuel (step fuel environment definition).environment rest).steps = _
      rw [finalEqual, stepEqual]
      exact append_assoc_exact environment first remaining

theorem project_binding_fields (nameCode : List Nat → Nat) (binding : Binding) :
    (projectBinding nameCode binding).name = nameCode binding.name ∧
    (projectBinding nameCode binding).type = encode binding.ty ∧
    (projectBinding nameCode binding).value = encode binding.value ∧
    (projectBinding nameCode binding).inferred = encode binding.inferred := ⟨rfl, rfl, rfl, rfl⟩

theorem project_append (nameCode : List Nat → Nat) (left right : Environment) :
    projectEnvironment nameCode (left ++ right) =
      projectEnvironment nameCode left ++ projectEnvironment nameCode right := by
  induction left with
  | nil => rfl
  | cons binding rest ih => exact congrArg (List.cons (projectBinding nameCode binding)) ih

theorem project_successful_insertion (nameCode : List Nat → Nat) (fuel : Nat)
    (environment : Environment) (definition : Definition) (stored : Expr)
    (success : checked fuel environment definition = .ok stored) :
    projectEnvironment nameCode (step fuel environment definition).environment =
      projectEnvironment nameCode environment ++
      [⟨nameCode definition.name, encode definition.ty, encode definition.value, encode stored⟩] := by
  rw [success_stores_exact_fields fuel environment definition stored success, project_append]
  rfl

theorem project_refusal_preserves_records (nameCode : List Nat → Nat) (fuel : Nat)
    (environment : Environment) (definition : Definition) (code : Nat)
    (refusal : checked fuel environment definition = .error code) :
    projectEnvironment nameCode (step fuel environment definition).environment = projectEnvironment nameCode environment := by
  rw [refusal_preserves_all_bindings fuel environment definition code refusal]

theorem projected_lookup_corresponds (nameCode : List Nat → Nat)
    (injective : ∀ a b, nameCode a = nameCode b → a = b)
    {environment : Environment} (certified : Certified environment) (name : List Nat) :
    GooseStoredBindings.lookup (nameCode name) (projectEnvironment nameCode environment) =
      (find environment name).map (projectBinding nameCode) := by
  induction certified with
  | empty => rfl
  | @append previous binding prior fresh valid ih =>
    rw [project_append]
    change GooseStoredBindings.lookup (nameCode name)
      (projectEnvironment nameCode previous ++ [projectBinding nameCode binding]) = _
    rw [GooseStoredBindings.lookup_snoc, find_snoc]
    change (if nameCode name = nameCode binding.name then some (projectBinding nameCode binding)
      else GooseStoredBindings.lookup (nameCode name) (projectEnvironment nameCode previous)) = _
    by_cases same : binding.name = name
    · rw [ite_eq_left (congrArg nameCode same.symm), ite_eq_left same]
      rfl
    · have different : nameCode name ≠ nameCode binding.name :=
        fun equal => same (injective _ _ equal).symm
      rw [ite_eq_right different, ite_eq_right same]
      exact ih

/-- Reuses the old full-record theorem on the exact projected append suffix. -/
theorem projected_trace_preserves_old_record (nameCode : List Nat → Nat) (fuel : Nat)
    (environment : Environment) (definitions : List Definition) (index : Nat)
    (binding : GooseStoredBindings.Binding)
    (old : GooseStoredBindings.bindingAt (projectEnvironment nameCode environment) index = some binding) :
    GooseStoredBindings.bindingAt
      (projectEnvironment nameCode (finalEnvironment environment (runFrom fuel environment definitions).steps))
      index = some binding := by
  obtain ⟨suffix, append⟩ := run_environment_prefix fuel environment definitions
  rw [append, project_append]
  exact GooseStoredBindings.bindingAt_append_preserves _ _ index binding old

theorem projected_trace_preserves_lookup (nameCode : List Nat → Nat)
    (injective : ∀ a b, nameCode a = nameCode b → a = b) (fuel : Nat)
    (environment : Environment) (definitions : List Definition) (certified : Certified environment)
    (name : List Nat) (binding : Binding) (old : find environment name = some binding) :
    GooseStoredBindings.lookup (nameCode name)
      (projectEnvironment nameCode (finalEnvironment environment (runFrom fuel environment definitions).steps)) =
      some (projectBinding nameCode binding) := by
  rw [projected_lookup_corresponds nameCode injective
    (run_final_environment_certified fuel environment definitions certified) name]
  rw [run_preserves_lookup fuel environment definitions name binding old]
  rfl

end GooseSemanticEnvironment

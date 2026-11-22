import Substitution

/-!
Typing and beta/zeta/delta conversion for the owned numeric-sort fragment.
Expressions, scope, lifting and substitution are the previously audited model.
The evaluator has an explicit *recursion-depth* budget, not native work fuel.
Successful executions are connected to independent relational rules below.
No general termination, subject reduction, native refinement, cache correctness,
eta, proof irrelevance, or full Lean-kernel compatibility is asserted.
-/
namespace GooseTypingConversion
open GooseExpressionDag GooseSubstitution

deriving instance DecidableEq for Expr

structure Binding where
  name : List Nat
  ty : Expr
  value : Expr
  inferred : Expr
  deriving Repr

structure Definition where
  name : List Nat
  ty : Expr
  value : Expr
  deriving Repr

abbrev Environment := List Binding
abbrev Context := List Expr
abbrev Result (α : Type) := Except Nat α

def find (environment : Environment) (name : List Nat) : Option Binding :=
  match environment with
  | [] => none
  | binding :: rest =>
    match find rest name with
    | some found => some found
    | none => if binding.name = name then some binding else none

def validate (environment : Environment) : Expr → Result Unit
  | .sort _ | .var _ => .ok ()
  | .const name => match find environment name with
      | none => .error 2
      | some _ => .ok ()
  | .app a b | .lam a b | .pi a b => do
      validate environment a
      validate environment b
  | .letE a b c => do
      validate environment a
      validate environment b
      validate environment c

def piLevel (domain codomain : Nat) : Nat :=
  if codomain = 0 then 0 else Nat.max domain codomain

def head : Nat → Environment → Expr → Result Expr
  | 0, _, _ => .error 9
  | fuel + 1, environment, expression =>
    match expression with
    | .const name => match find environment name with
        | none => .error 2
        | some binding => head fuel environment binding.value
    | .letE _ value body => head fuel environment (substitute value 0 body)
    | .app fn arg => match head fuel environment fn with
        | .error code => .error code
        | .ok reduced => match reduced with
            | .lam _ body => head fuel environment (substitute arg 0 body)
            | .sort n => .ok (.app (.sort n) arg)
            | .var n => .ok (.app (.var n) arg)
            | .const n => .ok (.app (.const n) arg)
            | .app a b => .ok (.app (.app a b) arg)
            | .pi a b => .ok (.app (.pi a b) arg)
            | .letE a b c => .ok (.app (.letE a b c) arg)
    | .sort n => .ok (.sort n)
    | .var n => .ok (.var n)
    | .lam a b => .ok (.lam a b)
    | .pi a b => .ok (.pi a b)

def normal : Nat → Environment → Expr → Result Expr
  | 0, _, _ => .error 9
  | fuel + 1, environment, expression => do
    let reduced ← head fuel environment expression
    match reduced with
    | .app a b => return .app (← normal fuel environment a) (← normal fuel environment b)
    | .lam a b => return .lam (← normal fuel environment a) (← normal fuel environment b)
    | .pi a b => return .pi (← normal fuel environment a) (← normal fuel environment b)
    | .sort n => return .sort n
    | .var n => return .var n
    | .const n => return .const n
    | .letE a b c => return .letE a b c

def convertible : Nat → Environment → Expr → Expr → Result Bool
  | 0, _, _, _ => .error 9
  | fuel + 1, environment, left, right => do
    let a ← normal fuel environment left
    let b ← normal fuel environment right
    return decide (a = b)

mutual
  def infer : Nat → Environment → Context → Expr → Result Expr
    | 0, _, _, _ => .error 9
    | fuel + 1, environment, context, expression =>
      match expression with
      | .sort level => .ok (.sort (level + 1))
      | .var index => match lookup context index with
          | none => .error 1
          | some domain => .ok (lift (index + 1) 0 domain)
      | .const name => match find environment name with
          | none => .error 2
          | some binding => .ok binding.ty
      | .lam domain body => do
          let _ ← sortLevel fuel environment context domain
          let bodyType ← infer fuel environment (domain :: context) body
          return .pi domain bodyType
      | .pi domain codomain => do
          let a ← sortLevel fuel environment context domain
          let b ← sortLevel fuel environment (domain :: context) codomain
          return .sort (piLevel a b)
      | .app fn arg => do
          let fnType ← infer fuel environment context fn
          let reduced ← head fuel environment fnType
          match reduced with
          | .pi domain codomain =>
            let argType ← infer fuel environment context arg
            let equalTypes ← convertible fuel environment argType domain
            match equalTypes with
            | true => return substitute arg 0 codomain
            | false => throw 6
          | .sort _ | .var _ | .const _ | .app _ _ | .lam _ _ | .letE _ _ _ => throw 5
      | .letE type value body => do
          let _ ← sortLevel fuel environment context type
          let valueType ← infer fuel environment context value
          let equalTypes ← convertible fuel environment valueType type
          match equalTypes with
          | true => infer fuel environment context (substitute value 0 body)
          | false => throw 6

  def sortLevel : Nat → Environment → Context → Expr → Result Nat
    | 0, _, _, _ => .error 9
    | fuel + 1, environment, context, expression => do
      let type ← infer fuel environment context expression
      let reduced ← head fuel environment type
      match reduced with
      | .sort level => return level
      | .var _ | .const _ | .app _ _ | .lam _ _ | .pi _ _ | .letE _ _ _ => throw 4
end

def checkValue (fuel : Nat) (environment : Environment) (definition : Definition) : Result Expr := do
  let _ ← sortLevel fuel environment [] definition.ty
  let actual ← infer fuel environment [] definition.value
  let inferred ← normal fuel environment actual
  let equalTypes ← convertible fuel environment inferred definition.ty
  match equalTypes with
  | true => return inferred
  | false => throw 6

def checked (fuel : Nat) (environment : Environment) (definition : Definition) : Result Expr :=
  match find environment definition.name with
  | some _ => .error 3
  | none =>
    match scopeCheck definition.ty 0 && scopeCheck definition.value 0 with
    | false => .error 1
    | true => do
      validate environment definition.ty
      validate environment definition.value
      checkValue fuel environment definition

def insert (environment : Environment) (definition : Definition) (inferred : Expr) : Environment :=
  environment ++ [⟨definition.name, definition.ty, definition.value, inferred⟩]

structure Step where
  name : List Nat
  outcome : Nat
  environment : Environment
  deriving Repr

def step (fuel : Nat) (environment : Environment) (definition : Definition) : Step :=
  match checked fuel environment definition with
  | .error code => ⟨definition.name, code, environment⟩
  | .ok inferred => ⟨definition.name, 0, insert environment definition inferred⟩

def fatal (code : Nat) : Bool := code == 1 || code == 9

structure Observation where
  steps : List Step
  halted : Bool
  acceptanceAuthority : Bool
  deriving Repr

def runFrom (fuel : Nat) (environment : Environment) : List Definition → Observation
  | [] => ⟨[], false, false⟩
  | definition :: rest =>
    let next := step fuel environment definition
    match fatal next.outcome with
    | true => ⟨[next], true, false⟩
    | false =>
      let remaining := runFrom fuel next.environment rest
      ⟨next :: remaining.steps, remaining.halted, false⟩

def observe (fuel : Nat) (definitions : List Definition) : Observation := runFrom fuel [] definitions

/- Independent big-step rules, without model fuel or native metadata. -/
def notLambda : Expr → Bool
  | .lam _ _ => false
  | .sort _ | .var _ | .const _ | .app _ _ | .pi _ _ | .letE _ _ _ => true

inductive HeadReduces (environment : Environment) : Expr → Expr → Prop where
  | sort (level) : HeadReduces environment (.sort level) (.sort level)
  | var (index) : HeadReduces environment (.var index) (.var index)
  | lam (domain body) : HeadReduces environment (.lam domain body) (.lam domain body)
  | pi (domain body) : HeadReduces environment (.pi domain body) (.pi domain body)
  | delta {name binding result} : find environment name = some binding →
      HeadReduces environment binding.value result → HeadReduces environment (.const name) result
  | zeta {type value body result} : HeadReduces environment (substitute value 0 body) result →
      HeadReduces environment (.letE type value body) result
  | beta {fn arg domain body result} : HeadReduces environment fn (.lam domain body) →
      HeadReduces environment (substitute arg 0 body) result →
      HeadReduces environment (.app fn arg) result
  | app {fn arg reduced} : HeadReduces environment fn reduced → notLambda reduced = true →
      HeadReduces environment (.app fn arg) (.app reduced arg)

inductive Normalizes (environment : Environment) : Expr → Expr → Prop where
  | sort {expression level} : HeadReduces environment expression (.sort level) →
      Normalizes environment expression (.sort level)
  | var {expression index} : HeadReduces environment expression (.var index) →
      Normalizes environment expression (.var index)
  | app {expression a b a' b'} : HeadReduces environment expression (.app a b) →
      Normalizes environment a a' → Normalizes environment b b' →
      Normalizes environment expression (.app a' b')
  | lam {expression a b a' b'} : HeadReduces environment expression (.lam a b) →
      Normalizes environment a a' → Normalizes environment b b' →
      Normalizes environment expression (.lam a' b')
  | pi {expression a b a' b'} : HeadReduces environment expression (.pi a b) →
      Normalizes environment a a' → Normalizes environment b b' →
      Normalizes environment expression (.pi a' b')

def Converts (environment : Environment) (left right : Expr) : Prop :=
  ∃ result, Normalizes environment left result ∧ Normalizes environment right result

mutual
  inductive Infers (environment : Environment) : Context → Expr → Expr → Prop where
    | sort (context level) : Infers environment context (.sort level) (.sort (level + 1))
    | var {context index domain} : lookup context index = some domain →
        Infers environment context (.var index) (lift (index + 1) 0 domain)
    | const {context name binding} : find environment name = some binding →
        Infers environment context (.const name) binding.ty
    | lam {context domain body level bodyType} : HasSort environment context domain level →
        Infers environment (domain :: context) body bodyType →
        Infers environment context (.lam domain body) (.pi domain bodyType)
    | pi {context domain codomain a b} : HasSort environment context domain a →
        HasSort environment (domain :: context) codomain b →
        Infers environment context (.pi domain codomain) (.sort (piLevel a b))
    | app {context fn arg fnType domain codomain argType} : Infers environment context fn fnType →
        HeadReduces environment fnType (.pi domain codomain) →
        Infers environment context arg argType → Converts environment argType domain →
        Infers environment context (.app fn arg) (substitute arg 0 codomain)
    | letE {context type value body level valueType result} : HasSort environment context type level →
        Infers environment context value valueType → Converts environment valueType type →
        Infers environment context (substitute value 0 body) result →
        Infers environment context (.letE type value body) result
  inductive HasSort (environment : Environment) : Context → Expr → Nat → Prop where
    | intro {context expression type level} : Infers environment context expression type →
        HeadReduces environment type (.sort level) → HasSort environment context expression level
end

theorem head_sound (fuel : Nat) (environment : Environment) (expression result : Expr)
    (success : head fuel environment expression = .ok result) :
    HeadReduces environment expression result := by
  induction fuel generalizing expression result with
  | zero => cases success
  | succ fuel ih =>
    cases expression with
    | sort level => cases success; exact .sort level
    | var index => cases success; exact .var index
    | lam domain body => cases success; exact .lam domain body
    | pi domain body => cases success; exact .pi domain body
    | const name =>
      cases found : find environment name with
      | none => simp only [head, found] at success; cases success
      | some binding =>
        simp only [head, found] at success
        exact .delta found (ih _ _ success)
    | letE type value body => exact .zeta (ih _ _ success)
    | app fn arg =>
      cases reduced : head fuel environment fn with
      | error code => simp only [head, reduced] at success; cases success
      | ok reducedFn =>
        have first := ih _ _ reduced
        cases reducedFn with
        | lam domain body =>
          simp only [head, reduced] at success
          exact .beta first (ih _ _ success)
        | sort level => simp only [head, reduced] at success; cases success; exact .app first rfl
        | var index => simp only [head, reduced] at success; cases success; exact .app first rfl
        | const name => simp only [head, reduced] at success; cases success; exact .app first rfl
        | app a b => simp only [head, reduced] at success; cases success; exact .app first rfl
        | pi a b => simp only [head, reduced] at success; cases success; exact .app first rfl
        | letE a b c => simp only [head, reduced] at success; cases success; exact .app first rfl

theorem head_result_not_constant (fuel : Nat) (environment : Environment) (expression : Expr)
    (name : List Nat) : head fuel environment expression ≠ .ok (.const name) := by
  intro success
  have reduces := head_sound fuel environment expression (.const name) success
  clear success
  generalize targetEq : Expr.const name = target at reduces
  induction reduces with
  | sort => cases targetEq
  | var => cases targetEq
  | lam => cases targetEq
  | pi => cases targetEq
  | delta found reduced ih => exact ih targetEq
  | zeta reduced ih => exact ih targetEq
  | beta first second ihFirst ihSecond => exact ihSecond targetEq
  | app first neutral ih => cases targetEq

theorem head_result_not_let (fuel : Nat) (environment : Environment) (expression type value body : Expr) :
    head fuel environment expression ≠ .ok (.letE type value body) := by
  intro success
  have reduces := head_sound fuel environment expression (.letE type value body) success
  clear success
  generalize targetEq : Expr.letE type value body = target at reduces
  induction reduces with
  | sort => cases targetEq
  | var => cases targetEq
  | lam => cases targetEq
  | pi => cases targetEq
  | delta found reduced ih => exact ih targetEq
  | zeta reduced ih => exact ih targetEq
  | beta first second ihFirst ihSecond => exact ihSecond targetEq
  | app first neutral ih => cases targetEq

theorem normal_sound (fuel : Nat) (environment : Environment) (expression result : Expr)
    (success : normal fuel environment expression = .ok result) :
    Normalizes environment expression result := by
  induction fuel generalizing expression result with
  | zero => cases success
  | succ fuel ih =>
    cases reduced : head fuel environment expression with
    | error code => simp only [normal, reduced, bind, Except.bind] at success; cases success
    | ok reducedExpr =>
      have first := head_sound fuel environment expression reducedExpr reduced
      cases reducedExpr with
      | sort level => simp only [normal, reduced, bind, Except.bind, pure, Except.pure] at success; cases success; exact .sort first
      | var index => simp only [normal, reduced, bind, Except.bind, pure, Except.pure] at success; cases success; exact .var first
      | const name => exact False.elim (head_result_not_constant fuel environment expression name reduced)
      | letE a b c => exact False.elim (head_result_not_let fuel environment expression a b c reduced)
      | app a b | lam a b | pi a b =>
        cases left : normal fuel environment a with
        | error code => simp only [normal, reduced, left, bind, Except.bind] at success; cases success
        | ok a' =>
          cases right : normal fuel environment b with
          | error code => simp only [normal, reduced, left, right, bind, Except.bind] at success; cases success
          | ok b' =>
            simp only [normal, reduced, left, right, bind, Except.bind, pure, Except.pure] at success
            cases success
            first
            | exact .app first (ih _ _ left) (ih _ _ right)
            | exact .lam first (ih _ _ left) (ih _ _ right)
            | exact .pi first (ih _ _ left) (ih _ _ right)

theorem convertible_sound (fuel : Nat) (environment : Environment) (left right : Expr)
    (success : convertible fuel environment left right = .ok true) : Converts environment left right := by
  cases fuel with
  | zero => cases success
  | succ fuel =>
    cases lhs : normal fuel environment left with
    | error code => simp only [convertible, lhs, bind, Except.bind] at success; cases success
    | ok a =>
      cases rhs : normal fuel environment right with
      | error code => simp only [convertible, lhs, rhs, bind, Except.bind] at success; cases success
      | ok b =>
        simp only [convertible, lhs, rhs, bind, Except.bind, pure, Except.pure] at success
        have equal : a = b := of_decide_eq_true (Except.ok.inj success)
        cases equal
        exact ⟨a, normal_sound _ _ _ _ lhs, normal_sound _ _ _ _ rhs⟩

theorem conversion_symmetric (environment : Environment) (left right : Expr)
    (conversion : Converts environment left right) : Converts environment right left := by
  obtain ⟨result, a, b⟩ := conversion
  exact ⟨result, b, a⟩

theorem inference_and_sort_sound (fuel : Nat) :
    (∀ (environment : Environment) (context : Context) (expression result : Expr),
      infer fuel environment context expression = .ok result → Infers environment context expression result) ∧
    (∀ (environment : Environment) (context : Context) (expression : Expr) (level : Nat),
      sortLevel fuel environment context expression = .ok level → HasSort environment context expression level) := by
  induction fuel with
  | zero =>
    constructor
    · intro _ _ _ _ h; cases h
    · intro _ _ _ _ h; cases h
  | succ fuel ih =>
    constructor
    · intro environment context expression result success
      cases expression with
      | sort level => cases success; exact .sort context level
      | var index =>
        cases found : lookup context index with
        | none => simp only [infer, found] at success; cases success
        | some domain => simp only [infer, found] at success; cases success; exact .var found
      | const name =>
        cases found : find environment name with
        | none => simp only [infer, found] at success; cases success
        | some binding => simp only [infer, found] at success; cases success; exact .const found
      | lam domain body =>
        cases domainResult : sortLevel fuel environment context domain with
        | error code => simp only [infer, domainResult, bind, Except.bind] at success; cases success
        | ok level =>
          cases bodyResult : infer fuel environment (domain :: context) body with
          | error code => simp only [infer, domainResult, bodyResult, bind, Except.bind] at success; cases success
          | ok bodyType =>
            simp only [infer, domainResult, bodyResult, bind, Except.bind, pure, Except.pure] at success
            cases success
            exact .lam (ih.2 _ _ _ _ domainResult) (ih.1 _ _ _ _ bodyResult)
      | pi domain codomain =>
        cases domainResult : sortLevel fuel environment context domain with
        | error code => simp only [infer, domainResult, bind, Except.bind] at success; cases success
        | ok a =>
          cases codomainResult : sortLevel fuel environment (domain :: context) codomain with
          | error code => simp only [infer, domainResult, codomainResult, bind, Except.bind] at success; cases success
          | ok b =>
            simp only [infer, domainResult, codomainResult, bind, Except.bind, pure, Except.pure] at success
            cases success
            exact .pi (ih.2 _ _ _ _ domainResult) (ih.2 _ _ _ _ codomainResult)
      | app fn arg =>
        cases fnResult : infer fuel environment context fn with
        | error code => simp only [infer, fnResult, bind, Except.bind] at success; cases success
        | ok fnType =>
          cases reducedResult : head fuel environment fnType with
          | error code => simp only [infer, fnResult, reducedResult, bind, Except.bind] at success; cases success
          | ok reduced =>
            cases reduced with
            | pi domain codomain =>
              cases argResult : infer fuel environment context arg with
              | error code => simp only [infer, fnResult, reducedResult, argResult, bind, Except.bind] at success; cases success
              | ok argType =>
                cases conversion : convertible fuel environment argType domain with
                | error code => simp only [infer, fnResult, reducedResult, argResult, conversion, bind, Except.bind] at success; cases success
                | ok equalTypes =>
                  cases equalTypes with
                  | false => simp only [infer, fnResult, reducedResult, argResult, conversion, bind, Except.bind] at success; cases success
                  | true =>
                    simp only [infer, fnResult, reducedResult, argResult, conversion, bind, Except.bind, pure, Except.pure] at success
                    cases success
                    exact .app (ih.1 _ _ _ _ fnResult) (head_sound _ _ _ _ reducedResult)
                      (ih.1 _ _ _ _ argResult) (convertible_sound _ _ _ _ conversion)
            | sort _ | var _ | const _ | app _ _ | lam _ _ | letE _ _ _ =>
              simp only [infer, fnResult, reducedResult, bind, Except.bind] at success
              cases success
      | letE type value body =>
        cases typeResult : sortLevel fuel environment context type with
        | error code => simp only [infer, typeResult, bind, Except.bind] at success; cases success
        | ok level =>
          cases valueResult : infer fuel environment context value with
          | error code => simp only [infer, typeResult, valueResult, bind, Except.bind] at success; cases success
          | ok valueType =>
            cases conversion : convertible fuel environment valueType type with
            | error code => simp only [infer, typeResult, valueResult, conversion, bind, Except.bind] at success; cases success
            | ok equalTypes =>
              cases equalTypes with
              | false => simp only [infer, typeResult, valueResult, conversion, bind, Except.bind] at success; cases success
              | true =>
                simp only [infer, typeResult, valueResult, conversion, bind, Except.bind] at success
                exact .letE (ih.2 _ _ _ _ typeResult) (ih.1 _ _ _ _ valueResult)
                  (convertible_sound _ _ _ _ conversion) (ih.1 _ _ _ _ success)
    · intro environment context expression level success
      cases typeResult : infer fuel environment context expression with
      | error code => simp only [sortLevel, typeResult, bind, Except.bind] at success; cases success
      | ok type =>
        cases reducedResult : head fuel environment type with
        | error code => simp only [sortLevel, typeResult, reducedResult, bind, Except.bind] at success; cases success
        | ok reduced =>
          cases reduced with
          | sort result =>
            simp only [sortLevel, typeResult, reducedResult, bind, Except.bind, pure, Except.pure] at success
            cases success
            exact .intro (ih.1 _ _ _ _ typeResult) (head_sound _ _ _ _ reducedResult)
          | var _ | const _ | app _ _ | lam _ _ | pi _ _ | letE _ _ _ =>
            simp only [sortLevel, typeResult, reducedResult, bind, Except.bind] at success
            cases success

theorem infer_sound (fuel : Nat) (environment : Environment) (context : Context) (expression result : Expr)
    (success : infer fuel environment context expression = .ok result) :
    Infers environment context expression result := (inference_and_sort_sound fuel).1 _ _ _ _ success

theorem sortLevel_sound (fuel : Nat) (environment : Environment) (context : Context) (expression : Expr)
    (level : Nat) (success : sortLevel fuel environment context expression = .ok level) :
    HasSort environment context expression level := (inference_and_sort_sound fuel).2 _ _ _ _ success

/-- The stored result is a normalization of an inferred type and is convertible
    to the original declared type; it need not equal that syntax. -/
theorem checkValue_sound (fuel : Nat) (environment : Environment) (definition : Definition)
    (stored : Expr) (success : checkValue fuel environment definition = .ok stored) :
    (∃ level, HasSort environment [] definition.ty level) ∧
    (∃ actual, Infers environment [] definition.value actual ∧ Normalizes environment actual stored) ∧
    Converts environment stored definition.ty := by
  cases sortResult : sortLevel fuel environment [] definition.ty with
  | error code => simp only [checkValue, sortResult, bind, Except.bind] at success; cases success
  | ok level =>
    cases inferResult : infer fuel environment [] definition.value with
    | error code => simp only [checkValue, sortResult, inferResult, bind, Except.bind] at success; cases success
    | ok actual =>
      cases normalResult : normal fuel environment actual with
      | error code => simp only [checkValue, sortResult, inferResult, normalResult, bind, Except.bind] at success; cases success
      | ok normalized =>
        cases conversion : convertible fuel environment normalized definition.ty with
        | error code => simp only [checkValue, sortResult, inferResult, normalResult, conversion, bind, Except.bind] at success; cases success
        | ok equalTypes =>
          cases equalTypes with
          | false => simp only [checkValue, sortResult, inferResult, normalResult, conversion, bind, Except.bind] at success; cases success
          | true =>
            simp only [checkValue, sortResult, inferResult, normalResult, conversion, bind, Except.bind, pure, Except.pure] at success
            cases success
            exact ⟨⟨level, sortLevel_sound _ _ _ _ _ sortResult⟩,
              ⟨actual, infer_sound _ _ _ _ _ inferResult, normal_sound _ _ _ _ normalResult⟩,
              convertible_sound _ _ _ _ conversion⟩

theorem checked_success_has_semantics (fuel : Nat) (environment : Environment) (definition : Definition)
    (stored : Expr) (success : checked fuel environment definition = .ok stored) :
    checkValue fuel environment definition = .ok stored := by
  cases found : find environment definition.name with
  | some binding => simp only [checked, found] at success; cases success
  | none =>
    cases scope : scopeCheck definition.ty 0 && scopeCheck definition.value 0 with
    | false => simp only [checked, found, scope] at success; cases success
    | true =>
      cases typeValid : validate environment definition.ty with
      | error code => simp only [checked, found, scope, typeValid, bind, Except.bind] at success; cases success
      | ok u =>
        cases u
        cases valueValid : validate environment definition.value with
        | error code => simp only [checked, found, scope, typeValid, valueValid, bind, Except.bind] at success; cases success
        | ok u =>
          cases u
          simpa only [checked, found, scope, typeValid, valueValid, bind, Except.bind] using success

theorem stored_inferred_converts_to_declared (fuel : Nat) (environment : Environment) (definition : Definition)
    (stored : Expr) (success : checked fuel environment definition = .ok stored) :
    Converts environment stored definition.ty :=
  (checkValue_sound fuel environment definition stored
    (checked_success_has_semantics fuel environment definition stored success)).2.2

theorem infer_sort_rule (fuel : Nat) (environment : Environment) (context : Context) (level : Nat) :
    infer (fuel + 1) environment context (.sort level) = .ok (.sort (level + 1)) := rfl

theorem infer_variable_lifts_context (fuel : Nat) (environment : Environment) (context : Context)
    (index : Nat) (domain : Expr) (found : lookup context index = some domain) :
    infer (fuel + 1) environment context (.var index) = .ok (lift (index + 1) 0 domain) := by
  rw [infer, found]

theorem infer_constant_uses_declared_type (fuel : Nat) (environment : Environment) (context : Context)
    (name : List Nat) (binding : Binding) (found : find environment name = some binding) :
    infer (fuel + 1) environment context (.const name) = .ok binding.ty := by
  rw [infer, found]

theorem delta_uses_original_value (fuel : Nat) (environment : Environment)
    (name : List Nat) (binding : Binding) (found : find environment name = some binding) :
    head (fuel + 1) environment (.const name) = head fuel environment binding.value := by
  rw [head, found]

theorem zeta_uses_capture_avoiding_substitution (fuel : Nat) (environment : Environment)
    (type value body : Expr) :
    head (fuel + 1) environment (.letE type value body) = head fuel environment (substitute value 0 body) := rfl

theorem beta_uses_capture_avoiding_substitution (fuel : Nat) (environment : Environment)
    (domain body arg : Expr) :
    head (fuel + 2) environment (.app (.lam domain body) arg) =
      head (fuel + 1) environment (substitute arg 0 body) := rfl

theorem beta_substitution_preserves_scope (depth : Nat) (body arg : Expr)
    (bodyScoped : Scoped (depth + 1) body) (argScoped : Scoped depth arg) :
    Scoped depth (substitute arg 0 body) := by
  exact substitute_scope body arg depth 0 bodyScoped argScoped

theorem pi_prop_is_impredicative (domain : Nat) : piLevel domain 0 = 0 := rfl

theorem pi_positive_is_max (domain codomain : Nat) (positive : codomain ≠ 0) :
    piLevel domain codomain = Nat.max domain codomain := by
  unfold piLevel
  exact ite_eq_right positive

theorem zero_budget_refuses_inference (environment : Environment) (context : Context) (expression : Expr) :
    infer 0 environment context expression = .error 9 := rfl

theorem zero_budget_refuses_conversion (environment : Environment) (left right : Expr) :
    convertible 0 environment left right = .error 9 := rfl

theorem duplicate_precedes_semantics (fuel : Nat) (environment : Environment) (definition : Definition)
    (binding : Binding) (found : find environment definition.name = some binding) :
    checked fuel environment definition = .error 3 := by
  rw [checked, found]

theorem refusal_preserves_all_bindings (fuel : Nat) (environment : Environment) (definition : Definition)
    (code : Nat) (refusal : checked fuel environment definition = .error code) :
    (step fuel environment definition).environment = environment := by
  unfold step
  rw [refusal]

theorem success_stores_exact_fields (fuel : Nat) (environment : Environment) (definition : Definition)
    (inferred : Expr) (success : checked fuel environment definition = .ok inferred) :
    (step fuel environment definition).environment =
      environment ++ [⟨definition.name, definition.ty, definition.value, inferred⟩] := by
  unfold step
  rw [success]
  rfl

theorem success_preserves_existing_prefix (fuel : Nat) (environment : Environment) (definition : Definition)
    (inferred : Expr) (success : checked fuel environment definition = .ok inferred) :
    ∃ suffix, (step fuel environment definition).environment = environment ++ suffix :=
  ⟨[⟨definition.name, definition.ty, definition.value, inferred⟩],
    success_stores_exact_fields fuel environment definition inferred success⟩

theorem validate_unknown_constant (environment : Environment) (name : List Nat)
    (missing : find environment name = none) : validate environment (.const name) = .error 2 := by
  rw [validate, missing]

theorem unknown_zeta_value_is_not_erased (environment : Environment) (type body : Expr) (name : List Nat)
    (typeValid : validate environment type = .ok ()) (missing : find environment name = none) :
    validate environment (.letE type (.const name) body) = .error 2 := by
  rw [validate, typeValid]
  change (validate environment (.const name)).bind (fun _ => validate environment body) = .error 2
  rw [validate_unknown_constant environment name missing]
  rfl

theorem unknown_beta_argument_is_not_erased (environment : Environment) (fn : Expr) (name : List Nat)
    (fnValid : validate environment fn = .ok ()) (missing : find environment name = none) :
    validate environment (.app fn (.const name)) = .error 2 := by
  rw [validate, fnValid]
  exact validate_unknown_constant environment name missing

theorem run_has_no_authority (fuel : Nat) (environment : Environment) (definitions : List Definition) :
    (runFrom fuel environment definitions).acceptanceAuthority = false := by
  cases definitions with
  | nil => rfl
  | cons definition rest =>
    simp only [runFrom]
    split <;> rfl

theorem fatal_step_stops_suffix (fuel : Nat) (environment : Environment) (definition : Definition)
    (rest : List Definition) (halts : fatal (step fuel environment definition).outcome = true) :
    (runFrom fuel environment (definition :: rest)).steps = [step fuel environment definition] := by
  unfold runFrom
  dsimp only
  rw [halts]

end GooseTypingConversion

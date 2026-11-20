import ExpressionDag

/-!
Unbounded structural lifting and capture-avoiding single-variable substitution.
These definitions match the index/cutoff rules of the native Goose operations;
they do not model raw allocation, caches, fuel, integer bounds, typing, or the
compiler. Native correspondence is a separately executed finite obligation.
-/
namespace GooseSubstitution
open GooseExpressionDag

def lift (amount cutoff : Nat) (expression : Expr) : Expr :=
  match expression with
  | .sort level => .sort level
  | .var index => if index < cutoff then .var index else .var (index + amount)
  | .const name => .const name
  | .app fn arg => .app (lift amount cutoff fn) (lift amount cutoff arg)
  | .lam domain body => .lam (lift amount cutoff domain) (lift amount (cutoff + 1) body)
  | .pi domain body => .pi (lift amount cutoff domain) (lift amount (cutoff + 1) body)
  | .letE type value body =>
      .letE (lift amount cutoff type) (lift amount cutoff value) (lift amount (cutoff + 1) body)
termination_by structural expression

def substitute (replacement : Expr) (cutoff : Nat) (expression : Expr) : Expr :=
  match expression with
  | .sort level => .sort level
  | .var index =>
      if index < cutoff then .var index
      else if index = cutoff then lift cutoff 0 replacement
      else .var (index - 1)
  | .const name => .const name
  | .app fn arg => .app (substitute replacement cutoff fn) (substitute replacement cutoff arg)
  | .lam domain body =>
      .lam (substitute replacement cutoff domain) (substitute replacement (cutoff + 1) body)
  | .pi domain body =>
      .pi (substitute replacement cutoff domain) (substitute replacement (cutoff + 1) body)
  | .letE type value body =>
      .letE (substitute replacement cutoff type) (substitute replacement cutoff value)
        (substitute replacement (cutoff + 1) body)
termination_by structural expression

theorem lift_var_below (amount cutoff index : Nat) (below : index < cutoff) :
    lift amount cutoff (.var index) = .var index := by
  unfold lift
  exact ite_eq_left below

theorem lift_var_at_or_above (amount cutoff index : Nat) (above : cutoff ≤ index) :
    lift amount cutoff (.var index) = .var (index + amount) := by
  unfold lift
  exact ite_eq_right (Nat.not_lt_of_ge above)

theorem lift_lambda (amount cutoff : Nat) (domain body : Expr) :
    lift amount cutoff (.lam domain body) =
      .lam (lift amount cutoff domain) (lift amount (cutoff + 1) body) := rfl

theorem lift_pi (amount cutoff : Nat) (domain body : Expr) :
    lift amount cutoff (.pi domain body) =
      .pi (lift amount cutoff domain) (lift amount (cutoff + 1) body) := rfl

theorem lift_let (amount cutoff : Nat) (type value body : Expr) :
    lift amount cutoff (.letE type value body) =
      .letE (lift amount cutoff type) (lift amount cutoff value) (lift amount (cutoff + 1) body) := rfl

theorem lift_zero (expression : Expr) (cutoff : Nat) : lift 0 cutoff expression = expression := by
  induction expression generalizing cutoff with
  | sort => rfl
  | var index =>
      by_cases below : index < cutoff
      · exact lift_var_below _ _ _ below
      · exact lift_var_at_or_above _ _ _ (Nat.le_of_not_gt below)
  | const => rfl
  | app fn arg ihf iha =>
      change Expr.app (lift 0 cutoff fn) (lift 0 cutoff arg) = _
      rw [ihf, iha]
  | lam domain body ihd ihb =>
      change Expr.lam (lift 0 cutoff domain) (lift 0 (cutoff + 1) body) = _
      rw [ihd, ihb]
  | pi domain body ihd ihb =>
      change Expr.pi (lift 0 cutoff domain) (lift 0 (cutoff + 1) body) = _
      rw [ihd, ihb]
  | letE type value body iht ihv ihb =>
      change Expr.letE (lift 0 cutoff type) (lift 0 cutoff value) (lift 0 (cutoff + 1) body) = _
      rw [iht, ihv, ihb]

theorem lift_add (expression : Expr) (first second cutoff : Nat) :
    lift second cutoff (lift first cutoff expression) = lift (first + second) cutoff expression := by
  induction expression generalizing cutoff with
  | sort => rfl
  | var index =>
      by_cases below : index < cutoff
      · rw [lift_var_below _ _ _ below, lift_var_below _ _ _ below, lift_var_below _ _ _ below]
      · have above := Nat.le_of_not_gt below
        rw [lift_var_at_or_above _ _ _ above,
            lift_var_at_or_above _ _ _ (Nat.le_trans above (Nat.le_add_right _ _)),
            lift_var_at_or_above _ _ _ above]
        exact congrArg Expr.var (Nat.add_assoc _ _ _)
  | const => rfl
  | app fn arg ihf iha =>
      change Expr.app (lift second cutoff (lift first cutoff fn))
        (lift second cutoff (lift first cutoff arg)) = _
      rw [ihf, iha]
      rfl
  | lam domain body ihd ihb =>
      change Expr.lam (lift second cutoff (lift first cutoff domain))
        (lift second (cutoff + 1) (lift first (cutoff + 1) body)) = _
      rw [ihd, ihb]
      rfl
  | pi domain body ihd ihb =>
      change Expr.pi (lift second cutoff (lift first cutoff domain))
        (lift second (cutoff + 1) (lift first (cutoff + 1) body)) = _
      rw [ihd, ihb]
      rfl
  | letE type value body iht ihv ihb =>
      change Expr.letE (lift second cutoff (lift first cutoff type))
        (lift second cutoff (lift first cutoff value))
        (lift second (cutoff + 1) (lift first (cutoff + 1) body)) = _
      rw [iht, ihv, ihb]
      rfl

theorem lift_preserves_height (expression : Expr) (amount cutoff : Nat) :
    height (lift amount cutoff expression) = height expression := by
  induction expression generalizing cutoff with
  | sort => rfl
  | var index =>
      by_cases below : index < cutoff
      · rw [lift_var_below _ _ _ below]
      · rw [lift_var_at_or_above _ _ _ (Nat.le_of_not_gt below)]
        rfl
  | const => rfl
  | app fn arg ihf iha =>
      change Nat.max (height (lift amount cutoff fn)) (height (lift amount cutoff arg)) + 1 = _
      rw [ihf, iha]
      rfl
  | lam domain body ihd ihb =>
      change Nat.max (height (lift amount cutoff domain)) (height (lift amount (cutoff + 1) body)) + 1 = _
      rw [ihd, ihb]
      rfl
  | pi domain body ihd ihb =>
      change Nat.max (height (lift amount cutoff domain)) (height (lift amount (cutoff + 1) body)) + 1 = _
      rw [ihd, ihb]
      rfl
  | letE type value body iht ihv ihb =>
      change Nat.max (height (lift amount cutoff type))
        (Nat.max (height (lift amount cutoff value)) (height (lift amount (cutoff + 1) body))) + 1 = _
      rw [iht, ihv, ihb]
      rfl

theorem lift_fixed_of_scoped (expression : Expr) (amount cutoff : Nat)
    (within : Scoped cutoff expression) : lift amount cutoff expression = expression := by
  induction within with
  | sort => rfl
  | var below => exact lift_var_below _ _ _ below
  | const => rfl
  | app hf ha ihf iha => change Expr.app _ _ = _; rw [ihf, iha]
  | lam hd hb ihd ihb => change Expr.lam _ _ = _; rw [ihd, ihb]
  | pi hd hb ihd ihb => change Expr.pi _ _ = _; rw [ihd, ihb]
  | letE ht hv hb iht ihv ihb => change Expr.letE _ _ _ = _; rw [iht, ihv, ihb]

theorem lift_closed (expression : Expr) (amount cutoff : Nat) (closed : Closed expression) :
    lift amount cutoff expression = expression :=
  lift_fixed_of_scoped expression amount cutoff (scoped_monotone expression 0 cutoff (Nat.zero_le _) closed)

theorem lift_scope (expression : Expr) (depth amount cutoff : Nat) (within : Scoped depth expression) :
    Scoped (depth + amount) (lift amount cutoff expression) := by
  induction within generalizing cutoff with
  | sort => exact Scoped.sort _ _
  | @var depth index below =>
      by_cases belowCutoff : index < cutoff
      · rw [lift_var_below _ _ _ belowCutoff]
        exact Scoped.var (Nat.lt_of_lt_of_le below (Nat.le_add_right _ _))
      · rw [lift_var_at_or_above _ _ _ (Nat.le_of_not_gt belowCutoff)]
        exact Scoped.var (Nat.add_lt_add_right below amount)
  | const => exact Scoped.const _ _
  | @app depth fn arg hf ha ihf iha =>
      exact Scoped.app (ihf cutoff) (iha cutoff)
  | @lam depth domain body hd hb ihd ihb =>
      have inside := ihb (cutoff + 1)
      rw [Nat.add_right_comm depth 1 amount] at inside
      exact Scoped.lam (ihd cutoff) inside
  | @pi depth domain body hd hb ihd ihb =>
      have inside := ihb (cutoff + 1)
      rw [Nat.add_right_comm depth 1 amount] at inside
      exact Scoped.pi (ihd cutoff) inside
  | @letE depth type value body ht hv hb iht ihv ihb =>
      have inside := ihb (cutoff + 1)
      rw [Nat.add_right_comm depth 1 amount] at inside
      exact Scoped.letE (iht cutoff) (ihv cutoff) inside

theorem lift_loose_bound (expression : Expr) (amount cutoff : Nat) :
    loose (lift amount cutoff expression) ≤ loose expression + amount :=
  (scoped_iff_loose _ _).1 (lift_scope expression (loose expression) amount cutoff
    ((scoped_iff_loose expression (loose expression)).2 (Nat.le_refl _)))

theorem substitute_var_below (replacement : Expr) (cutoff index : Nat) (below : index < cutoff) :
    substitute replacement cutoff (.var index) = .var index := by
  unfold substitute
  exact ite_eq_left below

theorem substitute_var_equal (replacement : Expr) (cutoff : Nat) :
    substitute replacement cutoff (.var cutoff) = lift cutoff 0 replacement := by
  unfold substitute
  rw [ite_eq_right (Nat.not_lt_of_ge (Nat.le_refl cutoff)), ite_eq_left (Eq.refl cutoff)]

theorem substitute_var_above (replacement : Expr) (cutoff index : Nat) (above : cutoff < index) :
    substitute replacement cutoff (.var index) = .var (index - 1) := by
  unfold substitute
  rw [ite_eq_right (Nat.not_lt_of_ge (Nat.le_of_lt above)), ite_eq_right (Nat.ne_of_gt above)]

theorem substitute_lambda (replacement domain body : Expr) (cutoff : Nat) :
    substitute replacement cutoff (.lam domain body) =
      .lam (substitute replacement cutoff domain) (substitute replacement (cutoff + 1) body) := rfl

theorem substitute_pi (replacement domain body : Expr) (cutoff : Nat) :
    substitute replacement cutoff (.pi domain body) =
      .pi (substitute replacement cutoff domain) (substitute replacement (cutoff + 1) body) := rfl

theorem substitute_let (replacement type value body : Expr) (cutoff : Nat) :
    substitute replacement cutoff (.letE type value body) =
      .letE (substitute replacement cutoff type) (substitute replacement cutoff value)
        (substitute replacement (cutoff + 1) body) := rfl

theorem substitute_fixed_of_scoped (expression replacement : Expr) (cutoff : Nat)
    (within : Scoped cutoff expression) : substitute replacement cutoff expression = expression := by
  induction within with
  | sort => rfl
  | var below => exact substitute_var_below _ _ _ below
  | const => rfl
  | app hf ha ihf iha => change Expr.app _ _ = _; rw [ihf, iha]
  | lam hd hb ihd ihb => change Expr.lam _ _ = _; rw [ihd, ihb]
  | pi hd hb ihd ihb => change Expr.pi _ _ = _; rw [ihd, ihb]
  | letE ht hv hb iht ihv ihb => change Expr.letE _ _ _ = _; rw [iht, ihv, ihb]

theorem substitute_closed (expression replacement : Expr) (cutoff : Nat) (closed : Closed expression) :
    substitute replacement cutoff expression = expression :=
  substitute_fixed_of_scoped expression replacement cutoff
    (scoped_monotone expression 0 cutoff (Nat.zero_le _) closed)

theorem substitute_scope (expression replacement : Expr) (ambient cutoff : Nat)
    (within : Scoped (ambient + cutoff + 1) expression) (replacementWithin : Scoped ambient replacement) :
    Scoped (ambient + cutoff) (substitute replacement cutoff expression) := by
  induction expression generalizing cutoff with
  | sort => exact Scoped.sort _ _
  | var index =>
      have bound := (variable_requires_exact_depth _ _).1 within
      by_cases below : index < cutoff
      · rw [substitute_var_below _ _ _ below]
        exact Scoped.var (Nat.lt_of_lt_of_le below (Nat.le_add_left _ _))
      · by_cases equal : index = cutoff
        · rw [equal, substitute_var_equal]
          exact lift_scope replacement ambient cutoff 0 replacementWithin
        · have above : cutoff < index := Nat.lt_of_le_of_ne (Nat.le_of_not_gt below) (Ne.symm equal)
          rw [substitute_var_above _ _ _ above]
          have positive := Nat.lt_of_le_of_lt (Nat.zero_le cutoff) above
          exact Scoped.var (Nat.lt_of_lt_of_le (Nat.sub_lt positive (Nat.zero_lt_succ 0))
            (Nat.le_of_lt_succ bound))
  | const => exact Scoped.const _ _
  | app fn arg ihf iha =>
      cases within with
      | app hf ha => exact Scoped.app (ihf cutoff hf) (iha cutoff ha)
  | lam domain body ihd ihb =>
      cases within with
      | lam hd hb =>
          have bodyWithin : Scoped (ambient + (cutoff + 1) + 1) body := by
            rw [← Nat.add_assoc ambient cutoff 1]
            exact hb
          have result := ihb (cutoff + 1) bodyWithin
          rw [← Nat.add_assoc ambient cutoff 1] at result
          exact Scoped.lam (ihd cutoff hd) result
  | pi domain body ihd ihb =>
      cases within with
      | pi hd hb =>
          have bodyWithin : Scoped (ambient + (cutoff + 1) + 1) body := by
            rw [← Nat.add_assoc ambient cutoff 1]
            exact hb
          have result := ihb (cutoff + 1) bodyWithin
          rw [← Nat.add_assoc ambient cutoff 1] at result
          exact Scoped.pi (ihd cutoff hd) result
  | letE type value body iht ihv ihb =>
      cases within with
      | letE ht hv hb =>
          have bodyWithin : Scoped (ambient + (cutoff + 1) + 1) body := by
            rw [← Nat.add_assoc ambient cutoff 1]
            exact hb
          have result := ihb (cutoff + 1) bodyWithin
          rw [← Nat.add_assoc ambient cutoff 1] at result
          exact Scoped.letE (iht cutoff ht) (ihv cutoff hv) result

theorem substitute_closed_top (expression replacement : Expr)
    (within : Scoped 1 expression) (replacementClosed : Closed replacement) :
    Closed (substitute replacement 0 expression) :=
  substitute_scope expression replacement 0 0 within replacementClosed

theorem substitute_lift_one (expression replacement : Expr) (cutoff : Nat) :
    substitute replacement cutoff (lift 1 cutoff expression) = expression := by
  induction expression generalizing cutoff with
  | sort => rfl
  | var index =>
      by_cases below : index < cutoff
      · rw [lift_var_below _ _ _ below, substitute_var_below _ _ _ below]
      · have above := Nat.le_of_not_gt below
        rw [lift_var_at_or_above _ _ _ above,
            substitute_var_above _ _ _ (Nat.lt_of_le_of_lt above (Nat.lt_succ_self index))]
        rfl
  | const => rfl
  | app fn arg ihf iha =>
      change Expr.app (substitute replacement cutoff (lift 1 cutoff fn))
        (substitute replacement cutoff (lift 1 cutoff arg)) = _
      rw [ihf, iha]
  | lam domain body ihd ihb =>
      change Expr.lam (substitute replacement cutoff (lift 1 cutoff domain))
        (substitute replacement (cutoff + 1) (lift 1 (cutoff + 1) body)) = _
      rw [ihd, ihb]
  | pi domain body ihd ihb =>
      change Expr.pi (substitute replacement cutoff (lift 1 cutoff domain))
        (substitute replacement (cutoff + 1) (lift 1 (cutoff + 1) body)) = _
      rw [ihd, ihb]
  | letE type value body iht ihv ihb =>
      change Expr.letE (substitute replacement cutoff (lift 1 cutoff type))
        (substitute replacement cutoff (lift 1 cutoff value))
        (substitute replacement (cutoff + 1) (lift 1 (cutoff + 1) body)) = _
      rw [iht, ihv, ihb]

theorem substitute_lift_one_top (expression replacement : Expr) :
    substitute replacement 0 (lift 1 0 expression) = expression :=
  substitute_lift_one expression replacement 0

/-- Inserting a slot immediately above the target, then substituting that
target by its own variable, is also the identity. This includes open terms. -/
theorem substitute_variable_after_lift (expression : Expr) (cutoff : Nat) :
    substitute (.var 0) cutoff (lift 1 (cutoff + 1) expression) = expression := by
  induction expression generalizing cutoff with
  | sort => rfl
  | var index =>
      by_cases below : index < cutoff
      · rw [lift_var_below _ _ _ (Nat.lt_trans below (Nat.lt_succ_self cutoff)),
            substitute_var_below _ _ _ below]
      · by_cases equal : index = cutoff
        · rw [equal, lift_var_below _ _ _ (Nat.lt_succ_self cutoff), substitute_var_equal,
              lift_var_at_or_above _ _ _ (Nat.zero_le 0), Nat.zero_add]
        · have above : cutoff < index := Nat.lt_of_le_of_ne (Nat.le_of_not_gt below) (Ne.symm equal)
          rw [lift_var_at_or_above _ _ _ above,
              substitute_var_above _ _ _ (Nat.lt_trans above (Nat.lt_succ_self index))]
          rfl
  | const => rfl
  | app fn arg ihf iha =>
      change Expr.app (substitute (.var 0) cutoff (lift 1 (cutoff + 1) fn))
        (substitute (.var 0) cutoff (lift 1 (cutoff + 1) arg)) = _
      rw [ihf, iha]
  | lam domain body ihd ihb =>
      change Expr.lam (substitute (.var 0) cutoff (lift 1 (cutoff + 1) domain))
        (substitute (.var 0) (cutoff + 1) (lift 1 ((cutoff + 1) + 1) body)) = _
      rw [ihd, ihb]
  | pi domain body ihd ihb =>
      change Expr.pi (substitute (.var 0) cutoff (lift 1 (cutoff + 1) domain))
        (substitute (.var 0) (cutoff + 1) (lift 1 ((cutoff + 1) + 1) body)) = _
      rw [ihd, ihb]
  | letE type value body iht ihv ihb =>
      change Expr.letE (substitute (.var 0) cutoff (lift 1 (cutoff + 1) type))
        (substitute (.var 0) cutoff (lift 1 (cutoff + 1) value))
        (substitute (.var 0) (cutoff + 1) (lift 1 ((cutoff + 1) + 1) body)) = _
      rw [iht, ihv, ihb]

theorem lambda_substitution_avoids_capture (replacement domain : Expr) (cutoff : Nat) :
    substitute replacement cutoff (.lam domain (.var (cutoff + 1))) =
      .lam (substitute replacement cutoff domain) (lift (cutoff + 1) 0 replacement) := by
  rw [substitute_lambda, substitute_var_equal]

theorem pi_substitution_avoids_capture (replacement domain : Expr) (cutoff : Nat) :
    substitute replacement cutoff (.pi domain (.var (cutoff + 1))) =
      .pi (substitute replacement cutoff domain) (lift (cutoff + 1) 0 replacement) := by
  rw [substitute_pi, substitute_var_equal]

theorem let_substitution_avoids_capture (replacement type value : Expr) (cutoff : Nat) :
    substitute replacement cutoff (.letE type value (.var (cutoff + 1))) =
      .letE (substitute replacement cutoff type) (substitute replacement cutoff value)
        (lift (cutoff + 1) 0 replacement) := by
  rw [substitute_let, substitute_var_equal]

/-- A structural test family with arbitrarily many binding levels. -/
def lambdaNest : Nat → Expr → Expr
  | 0, expression => expression
  | nesting + 1, expression => .lam (.sort 0) (lambdaNest nesting expression)

theorem nested_lambda_substitution_avoids_capture (replacement : Expr) (nesting cutoff : Nat) :
    substitute replacement cutoff (lambdaNest nesting (.var (cutoff + nesting))) =
      lambdaNest nesting (lift (cutoff + nesting) 0 replacement) := by
  induction nesting generalizing cutoff with
  | zero => exact substitute_var_equal _ _
  | succ nesting ih =>
      change Expr.lam (.sort 0)
        (substitute replacement (cutoff + 1) (lambdaNest nesting (.var (cutoff + (nesting + 1))))) =
        .lam (.sort 0) (lambdaNest nesting (lift (cutoff + (nesting + 1)) 0 replacement))
      rw [← Nat.add_assoc cutoff nesting 1, Nat.add_right_comm cutoff nesting 1, ih]

theorem nested_lambda_free_variable_stays_free (index nesting cutoff : Nat) :
    substitute (.var index) cutoff (lambdaNest nesting (.var (cutoff + nesting))) =
      lambdaNest nesting (.var (index + (cutoff + nesting))) := by
  rw [nested_lambda_substitution_avoids_capture,
      lift_var_at_or_above _ _ _ (Nat.zero_le index)]

/-- The parameter of substitution is a raw DAG reference. It is resolved
after decoding, without giving either transformation admission authority. -/
inductive Operation where
  | lift (amount : Nat)
  | substitute (replacement : Nat)
  deriving Repr

def transform (table : List Expr) (operation : Operation) (root cutoff : Nat) : Option Expr :=
  match lookup table root with
  | none => none
  | some expression =>
      match operation with
      | .lift amount => some (lift amount cutoff expression)
      | .substitute replacement =>
          match lookup table replacement with
          | none => none
          | some value => some (substitute value cutoff expression)

def observe (nodes : List RawNode) (operation : Operation) (root cutoff : Nat)
    (depths : List Nat) : Projection :=
  match decode nodes with
  | none => ⟨false, [], [], [], [], false⟩
  | some table =>
      match transform table operation root cutoff with
      | none => ⟨false, [], [], [], [], false⟩
      | some expression =>
          ⟨true, [encode expression], [height expression], [loose expression],
            [depths.map (scopeCheck expression)], false⟩

theorem refused_observation_is_empty (nodes : List RawNode) (operation : Operation)
    (root cutoff : Nat) (depths : List Nat) (refused : decode nodes = none) :
    observe nodes operation root cutoff depths = ⟨false, [], [], [], [], false⟩ := by
  unfold observe
  rw [refused]

theorem observe_has_no_authority (nodes : List RawNode) (operation : Operation)
    (root cutoff : Nat) (depths : List Nat) :
    (observe nodes operation root cutoff depths).acceptanceAuthority = false := by
  unfold observe
  cases decoded : decode nodes with
  | none => rfl
  | some table =>
      dsimp only
      cases transform table operation root cutoff <;> rfl

end GooseSubstitution

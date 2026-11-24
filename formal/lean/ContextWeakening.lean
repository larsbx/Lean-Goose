import EnvironmentScope

/-!
Typed weakening for the numeric-sort reference. Contexts are innermost first,
and each entry is expressed in its own outer tail. An insertion lifts the
entries newer than the inserted binder at their respective cutoffs.
-/
namespace GooseContextWeakening
open GooseExpressionDag GooseSubstitution GooseTypingConversion
open GooseSemanticEnvironment GooseEnvironmentScope

/-- Moving a lift below an existing block of new slots shifts its cutoff. -/
theorem lift_after_lift (expression : Expr) (width base cutoff : Nat) (order : base ≤ cutoff) :
    lift 1 (cutoff + width) (lift width base expression) =
      lift width base (lift 1 cutoff expression) := by
  induction expression generalizing base cutoff with
  | sort | const => rfl
  | var index =>
    by_cases older : cutoff ≤ index
    · rw [lift_var_at_or_above width base index (Nat.le_trans order older),
          lift_var_at_or_above 1 _ _ (Nat.add_le_add_right older width),
          lift_var_at_or_above 1 cutoff index older,
          lift_var_at_or_above width base (index + 1)
            (Nat.le_trans order (Nat.le_trans older (Nat.le_add_right index 1)))]
      exact congrArg Expr.var (Nat.add_right_comm _ _ _)
    · have newer := Nat.lt_of_not_ge older
      rw [lift_var_below 1 cutoff index newer]
      by_cases beforeBase : index < base
      · rw [lift_var_below width base index beforeBase,
            lift_var_below 1 _ _ (Nat.lt_of_lt_of_le newer (Nat.le_add_right _ _))]
      · rw [lift_var_at_or_above width base index (Nat.le_of_not_gt beforeBase),
            lift_var_below 1 _ _ (Nat.add_lt_add_right newer width)]
  | app fn arg ihFn ihArg =>
    change Expr.app _ _ = Expr.app _ _
    rw [ihFn base cutoff order, ihArg base cutoff order]
  | lam domain body ihDomain ihBody =>
    have under := ihBody (base + 1) (cutoff + 1) (Nat.succ_le_succ order)
    rw [Nat.add_right_comm cutoff 1 width] at under
    change Expr.lam _ _ = Expr.lam _ _
    rw [ihDomain base cutoff order, under]
  | pi domain body ihDomain ihBody =>
    have under := ihBody (base + 1) (cutoff + 1) (Nat.succ_le_succ order)
    rw [Nat.add_right_comm cutoff 1 width] at under
    change Expr.pi _ _ = Expr.pi _ _
    rw [ihDomain base cutoff order, under]
  | letE type value body ihType ihValue ihBody =>
    have under := ihBody (base + 1) (cutoff + 1) (Nat.succ_le_succ order)
    rw [Nat.add_right_comm cutoff 1 width] at under
    change Expr.letE _ _ _ = Expr.letE _ _ _
    rw [ihType base cutoff order, ihValue base cutoff order, under]

/-- Lifting outside a substitution also lifts the replacement. In the original
    body the lift skips the slot that the substitution will remove. -/
theorem lift_after_substitute (expression replacement : Expr) (cutoff depth : Nat) :
    lift 1 (cutoff + depth) (substitute replacement depth expression) =
      substitute (lift 1 cutoff replacement) depth (lift 1 (cutoff + depth + 1) expression) := by
  induction expression generalizing depth with
  | sort | const => rfl
  | var index =>
    by_cases below : index < depth
    · have beforeLift := Nat.lt_of_lt_of_le below (Nat.le_add_left depth cutoff)
      rw [substitute_var_below _ _ _ below, lift_var_below 1 _ _ beforeLift,
          lift_var_below 1 _ _ (Nat.lt_trans beforeLift (Nat.lt_succ_self _)),
          substitute_var_below _ _ _ below]
    · by_cases equal : index = depth
      · subst index
        rw [substitute_var_equal,
            lift_var_below 1 _ _ (Nat.lt_of_le_of_lt (Nat.le_add_left depth cutoff) (Nat.lt_succ_self _)),
            substitute_var_equal]
        exact lift_after_lift replacement depth 0 cutoff (Nat.zero_le _)
      · have above : depth < index := Nat.lt_of_le_of_ne (Nat.le_of_not_gt below) (Ne.symm equal)
        cases index with
        | zero => exact False.elim (Nat.not_lt_zero _ above)
        | succ index =>
          rw [substitute_var_above _ _ _ above]
          change lift 1 (cutoff + depth) (.var index) = _
          by_cases beforeLift : index < cutoff + depth
          · rw [lift_var_below 1 _ index beforeLift, lift_var_below 1 _ _ (Nat.succ_lt_succ beforeLift),
                substitute_var_above _ _ _ above]
            rfl
          · have afterLift := Nat.le_of_not_gt beforeLift
            rw [lift_var_at_or_above 1 _ index afterLift, lift_var_at_or_above 1 _ _ (Nat.succ_le_succ afterLift),
                substitute_var_above _ _ _ (Nat.lt_trans above (Nat.lt_succ_self _))]
            rfl
  | app fn arg ihFn ihArg =>
    change Expr.app _ _ = Expr.app _ _
    rw [ihFn depth, ihArg depth]
  | lam domain body ihDomain ihBody =>
    change Expr.lam (lift 1 (cutoff + depth) (substitute replacement depth domain))
      (lift 1 (cutoff + (depth + 1)) (substitute replacement (depth + 1) body)) = _
    rw [ihDomain depth, ihBody (depth + 1)]
    rfl
  | pi domain body ihDomain ihBody =>
    change Expr.pi (lift 1 (cutoff + depth) (substitute replacement depth domain))
      (lift 1 (cutoff + (depth + 1)) (substitute replacement (depth + 1) body)) = _
    rw [ihDomain depth, ihBody (depth + 1)]
    rfl
  | letE type value body ihType ihValue ihBody =>
    change Expr.letE (lift 1 (cutoff + depth) (substitute replacement depth type))
      (lift 1 (cutoff + depth) (substitute replacement depth value))
      (lift 1 (cutoff + (depth + 1)) (substitute replacement (depth + 1) body)) = _
    rw [ihType depth, ihValue depth, ihBody (depth + 1)]
    rfl

private theorem lift_after_substitute_top (expression replacement : Expr) (cutoff : Nat) :
    lift 1 cutoff (substitute replacement 0 expression) =
      substitute (lift 1 cutoff replacement) 0 (lift 1 (cutoff + 1) expression) :=
  lift_after_substitute expression replacement cutoff 0

private theorem notLambda_lift (expression : Expr) (cutoff : Nat) :
    notLambda (lift 1 cutoff expression) = notLambda expression := by
  cases expression with
  | var index =>
    by_cases below : index < cutoff
    · rw [lift_var_below _ _ _ below]
    · rw [lift_var_at_or_above _ _ _ (Nat.le_of_not_gt below)]
      rfl
  | sort | const | app | lam | pi | letE => rfl

theorem head_reduction_lift {environment : Environment} (values : LookupValuesClosed environment)
    {expression result : Expr} (reduction : HeadReduces environment expression result) (cutoff : Nat) :
    HeadReduces environment (lift 1 cutoff expression) (lift 1 cutoff result) := by
  induction reduction generalizing cutoff with
  | sort => exact .sort _
  | var index =>
    by_cases below : index < cutoff
    · rw [lift_var_below _ _ _ below]; exact .var _
    · rw [lift_var_at_or_above _ _ _ (Nat.le_of_not_gt below)]; exact .var _
  | lam => exact .lam _ _
  | pi => exact .pi _ _
  | @delta _ binding _ found _ ih =>
    have lifted := ih cutoff
    rw [lift_closed binding.value 1 cutoff (values _ _ found)] at lifted
    exact .delta found lifted
  | @zeta type value body _ _ ih =>
    have lifted := ih cutoff
    rw [lift_after_substitute_top] at lifted
    exact .zeta lifted
  | @beta fn arg domain body _ _ _ ihFn ihBody =>
    have lifted := ihBody cutoff
    rw [lift_after_substitute_top] at lifted
    exact .beta (ihFn cutoff) lifted
  | @app fn arg reduced _ neutral ih =>
    exact .app (ih cutoff) ((notLambda_lift reduced cutoff).trans neutral)

theorem normalization_lift {environment : Environment} (values : LookupValuesClosed environment)
    {expression result : Expr} (reduction : Normalizes environment expression result) (cutoff : Nat) :
    Normalizes environment (lift 1 cutoff expression) (lift 1 cutoff result) := by
  induction reduction generalizing cutoff with
  | sort first => exact .sort (head_reduction_lift values first cutoff)
  | var first =>
    rename_i index
    have lifted := head_reduction_lift values first cutoff
    by_cases below : index < cutoff
    · rw [lift_var_below _ _ _ below] at lifted ⊢; exact .var lifted
    · rw [lift_var_at_or_above _ _ _ (Nat.le_of_not_gt below)] at lifted ⊢; exact .var lifted
  | app first _ _ ihFn ihArg =>
    exact .app (head_reduction_lift values first cutoff) (ihFn cutoff) (ihArg cutoff)
  | lam first _ _ ihDomain ihBody =>
    exact .lam (head_reduction_lift values first cutoff) (ihDomain cutoff) (ihBody (cutoff + 1))
  | pi first _ _ ihDomain ihBody =>
    exact .pi (head_reduction_lift values first cutoff) (ihDomain cutoff) (ihBody (cutoff + 1))

theorem conversion_lift {environment : Environment} (values : LookupValuesClosed environment)
    {left right : Expr} (conversion : Converts environment left right) (cutoff : Nat) :
    Converts environment (lift 1 cutoff left) (lift 1 cutoff right) := by
  obtain ⟨result, leftNormal, rightNormal⟩ := conversion
  exact ⟨lift 1 cutoff result, normalization_lift values leftNormal cutoff,
    normalization_lift values rightNormal cutoff⟩

/-- Insert one binder whose annotation has scope, available constants and a
    sort in its own outer tail. Moving inward lifts each traversed annotation. -/
inductive ContextInsertion (environment : Environment) : Nat → Context → Context → Prop where
  | here {outer type level} : ScopedAvailable environment outer.length type →
      HasSort environment outer type level → ContextInsertion environment 0 outer (type :: outer)
  | under {cutoff before after} (type : Expr) : ContextInsertion environment cutoff before after →
      ContextInsertion environment (cutoff + 1) (type :: before) (lift 1 cutoff type :: after)

theorem ContextInsertion.cutoff_length {environment : Environment} {cutoff : Nat} {before after : Context}
    (insertion : ContextInsertion environment cutoff before after) :
    cutoff ≤ before.length ∧ after.length = before.length + 1 := by
  induction insertion with
  | here => exact ⟨Nat.zero_le _, rfl⟩
  | under _ _ ih => exact ⟨Nat.succ_le_succ ih.1, congrArg Nat.succ ih.2⟩

/-- The transported index and the annotation fetched at that index yield
    exactly the lift of the original inferred variable type. -/
theorem ContextInsertion.lookup_lift {environment : Environment} {cutoff index : Nat}
    {before after : Context} {type : Expr} (insertion : ContextInsertion environment cutoff before after)
    (found : lookup before index = some type) :
    ∃ newIndex newType, lift 1 cutoff (.var index) = .var newIndex ∧
      lookup after newIndex = some newType ∧
      lift 1 cutoff (lift (index + 1) 0 type) = lift (newIndex + 1) 0 newType := by
  induction insertion generalizing index with
  | here =>
    exact ⟨index + 1, type, lift_var_at_or_above _ _ _ (Nat.zero_le _), found, lift_add _ _ _ _⟩
  | @under cutoff before after entry _ ih =>
    cases index with
    | zero =>
      change some entry = some type at found
      cases found
      exact ⟨0, lift 1 cutoff type, lift_var_below _ _ _ (Nat.zero_lt_succ _), rfl,
        lift_after_lift type 1 0 cutoff (Nat.zero_le _)⟩
    | succ index =>
      obtain ⟨newIndex, newType, shifted, newFound, equalTypes⟩ := ih (index := index) found
      refine ⟨newIndex + 1, newType, ?_, newFound, ?_⟩
      · rw [← lift_var_at_or_above 1 0 index (Nat.zero_le _),
            lift_after_lift (.var index) 1 0 cutoff (Nat.zero_le _), shifted,
            lift_var_at_or_above 1 0 newIndex (Nat.zero_le _)]
      · rw [← lift_add type (index + 1) 1 0,
            lift_after_lift (lift (index + 1) 0 type) 1 0 cutoff (Nat.zero_le _),
            equalTypes, lift_add]

private theorem inference_lift_aux {environment : Environment} (values : LookupValuesClosed environment)
    (types : ∀ name binding, find environment name = some binding → Closed binding.ty)
    {before : Context} {expression type : Expr} (inference : Infers environment before expression type) :
    ∀ {cutoff after}, ContextInsertion environment cutoff before after →
      Infers environment after (lift 1 cutoff expression) (lift 1 cutoff type) := by
  induction inference using Infers.rec (motive_2 := fun before expression level _ =>
    ∀ {cutoff after}, ContextInsertion environment cutoff before after →
      HasSort environment after (lift 1 cutoff expression) level) with
  | sort => exact fun _ => .sort _ _
  | var found =>
    intro cutoff after insertion
    obtain ⟨_, _, shifted, newFound, equalTypes⟩ := insertion.lookup_lift found
    rw [shifted, equalTypes]
    exact .var newFound
  | const found =>
    intro cutoff after _
    rw [lift_closed _ 1 cutoff (types _ _ found)]
    exact .const found
  | lam _ _ ihDomain ihBody =>
    exact fun insertion => .lam (ihDomain insertion) (ihBody (.under _ insertion))
  | pi _ _ ihDomain ihCodomain =>
    exact fun insertion => .pi (ihDomain insertion) (ihCodomain (.under _ insertion))
  | app _ reduced _ conversion ihFn ihArg =>
    intro cutoff after insertion
    rw [lift_after_substitute_top]
    exact .app (ihFn insertion) (head_reduction_lift values reduced cutoff) (ihArg insertion)
      (conversion_lift values conversion cutoff)
  | letE _ _ conversion _ ihType ihValue ihBody =>
    intro cutoff after insertion
    have liftedBody := ihBody insertion
    rw [lift_after_substitute_top] at liftedBody
    exact .letE (ihType insertion) (ihValue insertion) (conversion_lift values conversion cutoff) liftedBody
  | intro _ reduced ih =>
    exact .intro (ih ‹ContextInsertion _ _ _ _›) (head_reduction_lift values reduced _)

/-- Inference transports its exact output syntax under binder insertion. -/
theorem inference_lift {environment : Environment} (certified : Certified environment)
    {before after : Context} {cutoff : Nat} {expression type : Expr}
    (insertion : ContextInsertion environment cutoff before after)
    (inference : Infers environment before expression type) :
    Infers environment after (lift 1 cutoff expression) (lift 1 cutoff type) :=
  inference_lift_aux (lookup_values_closed_of_certified certified)
    (fun _ _ found => (certified_lookup_valid certified _ _ found).typeClosed) inference insertion

theorem sort_lift {environment : Environment} (certified : Certified environment)
    {before after : Context} {cutoff : Nat} {expression : Expr} {level : Nat}
    (insertion : ContextInsertion environment cutoff before after)
    (sort : HasSort environment before expression level) :
    HasSort environment after (lift 1 cutoff expression) level := by
  cases sort with
  | intro inference reduced =>
    exact .intro (inference_lift certified insertion inference)
      (head_reduction_lift (lookup_values_closed_of_certified certified) reduced cutoff)

/-- Every retained annotation has scope and a sort in its transported outer tail. -/
theorem ContextInsertion.preserves_valid {environment : Environment} (certified : Certified environment)
    {before after : Context} {cutoff : Nat} (insertion : ContextInsertion environment cutoff before after)
    (valid : ContextValid environment before) : ContextValid environment after := by
  induction insertion with
  | here within sort => exact .cons valid within sort
  | @under cutoff before after entry insertion ih =>
    cases valid with
    | cons valid within sort =>
      exact .cons (ih valid) ⟨insertion.cutoff_length.2 ▸ lift_scope _ _ _ _ within.1,
        lift_preserves_available within.2 1 cutoff⟩ (sort_lift certified insertion sort)

/-- The replacement remains typable against its transported annotation as
    substitution crosses a valid prefix of newer binders. -/
theorem substitution_hit {environment : Environment} (certified : Certified environment)
    {outer newer : Context} {replacement actual annotation : Expr}
    (valid : ContextValid environment (newer ++ outer))
    (typing : Infers environment outer replacement actual)
    (conversion : Converts environment actual annotation) :
    Infers environment (newer ++ outer) (substitute replacement newer.length (.var newer.length))
      (lift newer.length 0 actual) ∧
      Converts environment (lift newer.length 0 actual)
        (substitute replacement newer.length (lift (newer.length + 1) 0 annotation)) := by
  have lifted : Infers environment (newer ++ outer) (lift newer.length 0 replacement)
      (lift newer.length 0 actual) ∧
      Converts environment (lift newer.length 0 actual) (lift newer.length 0 annotation) := by
    induction newer with
    | nil =>
      rw [List.length_nil, List.nil_append, lift_zero, lift_zero, lift_zero]
      exact ⟨typing, conversion⟩
    | cons entry rest ih =>
      change ContextValid environment (entry :: (rest ++ outer)) at valid
      cases valid with
      | cons outerValid within sort =>
        obtain ⟨typed, converts⟩ := ih outerValid
        change Infers environment (entry :: (rest ++ outer)) (lift (rest.length + 1) 0 replacement)
          (lift (rest.length + 1) 0 actual) ∧
          Converts environment (lift (rest.length + 1) 0 actual) (lift (rest.length + 1) 0 annotation)
        rw [← lift_add replacement rest.length 1 0, ← lift_add actual rest.length 1 0,
            ← lift_add annotation rest.length 1 0]
        exact ⟨inference_lift certified (.here within sort) typed,
          conversion_lift (lookup_values_closed_of_certified certified) converts 0⟩
  have shifted := lift_after_lift annotation newer.length 0 0 (Nat.le_refl 0)
  rw [Nat.zero_add, lift_add, Nat.add_comm 1 newer.length] at shifted
  rw [substitute_var_equal, ← shifted, substitute_lift_one]
  exact lifted

/-- Literal beta exposes a body derivation and a convertible argument at the
    binder annotation. The expected result is the instantiated codomain. -/
theorem literal_beta_premises {environment : Environment} {context : Context}
    {domain body arg result : Expr}
    (typing : Infers environment context (.app (.lam domain body) arg) result) :
    ∃ level bodyType argType, HasSort environment context domain level ∧
      Infers environment (domain :: context) body bodyType ∧
      Infers environment context arg argType ∧ Converts environment argType domain ∧
      result = substitute arg 0 bodyType := by
  cases typing with
  | app fn head arg conversion =>
    cases fn with
    | lam sort bodyTyping =>
      cases head
      exact ⟨_, _, _, sort, bodyTyping, arg, conversion, rfl⟩

theorem zeta_inference {environment : Environment} {context : Context} {type value body result : Expr}
    (typing : Infers environment context (.letE type value body) result) :
    Infers environment context (substitute value 0 body) result := by
  cases typing with
  | letE _ _ _ bodyTyping => exact bodyTyping

theorem zeta_sort {environment : Environment} {context : Context} {type value body : Expr} {level : Nat}
    (typing : HasSort environment context (.letE type value body) level) :
    HasSort environment context (substitute value 0 body) level := by
  cases typing with
  | intro inference head => exact .intro (zeta_inference inference) head

end GooseContextWeakening

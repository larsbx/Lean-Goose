import ContextWeakening

namespace GooseContextWeakening
open GooseExpressionDag GooseSubstitution GooseTypingConversion
open GooseSemanticEnvironment GooseEnvironmentScope

private theorem sort_has_sort (context : Context) (level : Nat) :
    HasSort [] context (.sort level) (level + 1) := .intro (.sort context level) (.sort _)

private theorem sort_refl (level : Nat) : Converts [] (.sort level) (.sort level) :=
  ⟨_, .sort (.sort level), .sort (.sort level)⟩

private theorem var_refl (index : Nat) : Converts [] (.var index) (.var index) :=
  ⟨_, .var (.var index), .var (.var index)⟩

private theorem family_sort : HasSort [] [.sort 1] (.var 0) 1 :=
  .intro (.var (index := 0) (domain := .sort 1) rfl) (.sort 1)

private theorem family_scoped : ScopedAvailable [] 1 (.var 0) :=
  ⟨.var (Nat.zero_lt_succ 0), trivial⟩

private theorem source_valid : ContextValid [] [.var 0, .sort 1] :=
  .cons (.cons .empty ⟨.sort _ _, trivial⟩ (sort_has_sort [] 1)) family_scoped family_sort

private theorem middle_insertion : ContextInsertion [] 1 [.var 0, .sort 1] [.var 1, .var 0, .sort 1] :=
  .under (.var 0) (.here family_scoped family_sort)

/-- Starting with x : A and A : Sort 1, insert y : A between x and A. The
    retained x now points past y; the older A moves from index 1 to 2. -/
theorem middle_insertion_transports_dependent_lookup :
    ContextValid [] [.var 1, .var 0, .sort 1] ∧
    Infers [] [.var 1, .var 0, .sort 1] (.var 0) (.var 2) ∧
    HasSort [] [.var 1, .var 0, .sort 1] (.var 2) 1 := by
  have x : Infers [] [.var 0, .sort 1] (.var 0) (.var 1) :=
    .var (index := 0) (domain := .var 0) rfl
  have a : HasSort [] [.var 0, .sort 1] (.var 1) 1 :=
    .intro (.var (index := 1) (domain := .sort 1) rfl) (.sort 1)
  exact ⟨middle_insertion.preserves_valid .empty source_valid, inference_lift .empty middle_insertion x,
    sort_lift .empty middle_insertion a⟩

/-- A polymorphic identity is instantiated at A and then applied to x.
    The outer parameter shifts while both locally bound variables stay put. -/
theorem middle_insertion_transports_dependent_application :
    Infers [] [.var 1, .var 0, .sort 1]
      (.app (.app (.lam (.sort 1) (.lam (.var 0) (.var 0))) (.var 2)) (.var 0)) (.var 2) := by
  let context : Context := [.var 0, .sort 1]
  have localFamily : HasSort [] (.sort 1 :: context) (.var 0) 1 :=
    .intro (.var (index := 0) (domain := .sort 1) rfl) (.sort 1)
  have localValue : Infers [] (.var 0 :: .sort 1 :: context) (.var 0) (.var 1) :=
    .var (index := 0) (domain := .var 0) rfl
  have polymorphic : Infers [] context (.lam (.sort 1) (.lam (.var 0) (.var 0)))
      (.pi (.sort 1) (.pi (.var 0) (.var 1))) :=
    .lam (sort_has_sort context 1) (.lam localFamily localValue)
  have parameter : Infers [] context (.var 1) (.sort 1) :=
    .var (index := 1) (domain := .sort 1) rfl
  have instanceTyping : Infers [] context
      (.app (.lam (.sort 1) (.lam (.var 0) (.var 0))) (.var 1)) (.pi (.var 1) (.var 2)) :=
    .app polymorphic (.pi _ _) parameter (sort_refl 1)
  have arg : Infers [] context (.var 0) (.var 1) :=
    .var (index := 0) (domain := .var 0) rfl
  have application : Infers [] context
      (.app (.app (.lam (.sort 1) (.lam (.var 0) (.var 0))) (.var 1)) (.var 0)) (.var 1) :=
    .app instanceTyping (.pi _ _) arg (var_refl 1)
  exact inference_lift .empty middle_insertion application

/-- Insertion under two dependent entries and then under a let and Pi. -/
theorem deep_insertion_transports_let_sort :
    ContextValid [] [.var 2, .var 1, .sort 1, .sort 1] ∧
    HasSort [] [.var 2, .var 1, .sort 1, .sort 1]
      (.letE (.var 3) (.var 0) (.pi (.var 4) (.var 5))) 1 := by
  let context : Context := [.var 1, .var 0, .sort 1]
  have a := middle_insertion_transports_dependent_lookup.2.2
  have inPi : HasSort [] (.var 2 :: context) (.var 3) 1 :=
    .intro (.var (index := 3) (domain := .sort 1) rfl) (.sort 1)
  have piTyping : Infers [] context (.pi (.var 2) (.var 3)) (.sort 1) := .pi a inPi
  have letTyping : HasSort [] context (.letE (.var 2) (.var 0) (.pi (.var 3) (.var 4))) 1 :=
    .intro (.letE a middle_insertion_transports_dependent_lookup.2.1 (var_refl 2) piTyping) (.sort 1)
  have insertion : ContextInsertion [] 2 context [.var 2, .var 1, .sort 1, .sort 1] :=
    .under (.var 1) (.under (.var 0) (.here ⟨.sort _ _, trivial⟩ (sort_has_sort [.sort 1] 1)))
  exact ⟨insertion.preserves_valid .empty middle_insertion_transports_dependent_lookup.1,
    sort_lift .empty insertion letTyping⟩

/-- Copying the retained x annotation verbatim makes x depend on the
    newly inserted term y as if y were a type. All indices are still scoped. -/
theorem stale_annotation_scoped_but_invalid :
    ContextScoped [] [.var 0, .var 0, .sort 1] ∧ ¬ ContextValid [] [.var 0, .var 0, .sort 1] := by
  refine ⟨.cons source_valid.scoped ⟨.var (Nat.zero_lt_succ _), trivial⟩, ?_⟩
  intro valid
  cases valid with
  | cons _ _ sorts =>
    cases sorts with
    | intro inferred reduced =>
      cases inferred with
      | var found =>
        change some (Expr.var 0) = some _ at found
        cases found
        cases reduced

theorem self_referential_insertion_refused : ¬ ContextInsertion [] 0 [] [.var 0] := by
  intro insertion
  cases insertion with
  | here within _ =>
    exact Nat.not_lt_zero 0 ((variable_requires_exact_depth _ _).1 within.1)

theorem unsorted_insertion_refused :
    ScopedAvailable [] 0 (.lam (.sort 1) (.var 0)) ∧
      ¬ ContextInsertion [] 0 [] [.lam (.sort 1) (.var 0)] := by
  refine ⟨⟨.lam (.sort _ _) (.var (Nat.zero_lt_succ _)), ⟨trivial, trivial⟩⟩, ?_⟩
  intro insertion
  cases insertion with
  | here within sorts => exact scoped_context_can_lack_sort.2 (.cons .empty within sorts)

/-- A raw binding with an open declared type defeats exact lift at a constant.
    Such a binding cannot be supplied by a certified environment. -/
theorem open_constant_type_breaks_weakening :
    let environment : Environment := [⟨[65], .var 0, .sort 0, .sort 1⟩]
    ContextInsertion environment 0 [.sort 1] [.sort 1, .sort 1] ∧
      Infers environment [.sort 1] (.const [65]) (.var 0) ∧
      ¬ Infers environment [.sort 1, .sort 1] (.const [65]) (.var 1) := by
  let binding : Binding := ⟨[65], .var 0, .sort 0, .sort 1⟩
  refine ⟨.here ⟨.sort _ _, trivial⟩ (.intro (.sort _ 1) (.sort 2)),
    .const (binding := binding) rfl, ?_⟩
  intro typing
  generalize equal : Expr.var 1 = type at typing
  cases typing with
  | const found =>
    change some binding = some _ at found
    cases found
    cases equal

/-- An open original value can break lifting of a delta step even when the
    declared type is closed. -/
theorem open_delta_value_breaks_reduction_lift :
    let environment : Environment := [⟨[65], .sort 1, .var 0, .sort 1⟩]
    HeadReduces environment (.const [65]) (.var 0) ∧
      ¬ HeadReduces environment (.const [65]) (.var 1) := by
  exact ⟨.delta rfl (.var 0), by
    intro reduction
    cases reduction with
    | delta found reduced =>
      cases found
      cases reduced⟩

private def reducibleDomain : Expr := .letE (.sort 1) (.sort 0) (.sort 1)

/-- Even in the empty certified environment and context, exact inference of
    the redex's expected type can fail after beta. The reduct's type converts. -/
theorem literal_beta_requires_conversion :
    Infers [] [] (.app (.lam reducibleDomain (.var 0)) (.sort 0)) reducibleDomain ∧
      HeadReduces [] (.app (.lam reducibleDomain (.var 0)) (.sort 0)) (.sort 0) ∧
      (¬ Infers [] [] (.sort 0) reducibleDomain) ∧
      (∃ actual, Infers [] [] (.sort 0) actual ∧ Converts [] actual reducibleDomain) := by
  have domainSort : HasSort [] [] reducibleDomain 2 :=
    .intro (.letE (sort_has_sort [] 1) (.sort [] 0) (sort_refl 1) (.sort [] 1)) (.sort 2)
  have conversion : Converts [] (.sort 1) reducibleDomain :=
    ⟨.sort 1, .sort (.sort 1), .sort (.zeta (.sort 1))⟩
  have fn : Infers [] [] (.lam reducibleDomain (.var 0)) (.pi reducibleDomain reducibleDomain) :=
    .lam domainSort (.var (index := 0) (domain := reducibleDomain) rfl)
  refine ⟨.app fn (.pi _ _) (.sort [] 0) conversion, .beta (.lam _ _) (.sort 0), ?_,
    ⟨.sort 1, .sort [] 0, conversion⟩⟩
  intro typing
  cases typing

private def sortIdentity : Expr := .lam (.sort 1) (.var 0)

/-- Instantiating a head-normal neutral application may expose a beta redex,
    even when the replacement has the exact type declared for the slot. -/
theorem substitution_can_unblock_neutral_head :
    Infers [] [] sortIdentity (.pi (.sort 1) (.sort 1)) ∧
      Infers [] [.pi (.sort 1) (.sort 1)] (.app (.var 0) (.sort 0)) (.sort 1) ∧
      HeadReduces [] (.app (.var 0) (.sort 0)) (.app (.var 0) (.sort 0)) ∧
      HeadReduces [] (substitute sortIdentity 0 (.app (.var 0) (.sort 0))) (.sort 0) ∧
      ¬ HeadReduces [] (substitute sortIdentity 0 (.app (.var 0) (.sort 0)))
          (substitute sortIdentity 0 (.app (.var 0) (.sort 0))) := by
  have fn : Infers [] [.pi (.sort 1) (.sort 1)] (.var 0) (.pi (.sort 1) (.sort 1)) :=
    .var (index := 0) (domain := .pi (.sort 1) (.sort 1)) rfl
  refine ⟨.lam (sort_has_sort [] 1) (.var (index := 0) (domain := .sort 1) rfl),
    .app fn (.pi _ _) (.sort _ 0) (sort_refl 1),
    .app (.var 0) rfl, .beta (.lam _ _) (.sort 0), ?_⟩
  change ¬ HeadReduces [] (.app sortIdentity (.sort 0)) (.app sortIdentity (.sort 0))
  intro reduction
  cases reduction with
  | beta head body =>
    cases head
    cases body
  | app head neutral =>
    cases head
    cases neutral

end GooseContextWeakening

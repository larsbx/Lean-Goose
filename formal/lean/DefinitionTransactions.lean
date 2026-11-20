import Init

/-!
Ordered definition transactions for Lean-Goose's bounded observation profile.

The semantic checks are represented by four action kinds. This is an executable
abstract model, not a formalization of arbitrary Goose expression inference,
substitution, cache behavior, parser safety, or compiler correctness. Names are
unbounded natural numbers; the finite runtime profile uses names zero and one.
-/
namespace GooseTransactions

inductive Kind where
  | good | mismatch | alias | scope
  deriving Repr

structure Action where
  kind : Kind
  name : Nat
  target : Nat := 0
  deriving Repr

structure Observation where
  name : Nat
  code : Nat
  deriving Repr

structure State where
  environment : List Nat
  outcomes : List Observation
  halted : Bool
  acceptanceAuthority : Bool
  deriving Repr

structure Receipt where
  outcomes : List Observation
  successes : Nat
  acceptanceAuthority : Bool
  deriving Repr

/-- Constructive membership avoids importing quotient-based decision proofs. -/
def memberDecidable (name : Nat) : (xs : List Nat) → Decidable (name ∈ xs)
  | [] => isFalse (fun member => nomatch member)
  | head :: tail =>
    match Nat.decEq name head with
    | isTrue equal => isTrue (by rw [equal]; exact List.Mem.head _)
    | isFalse different =>
      match memberDecidable name tail with
      | isTrue member => isTrue (List.Mem.tail head member)
      | isFalse absent =>
        isFalse (fun member => by
          cases member with
          | head => exact different rfl
          | tail _ rest => exact absent rest)

local instance transactionMembership (name : Nat) (xs : List Nat) : Decidable (name ∈ xs) :=
  memberDecidable name xs

def initial : State := ⟨[], [], false, false⟩

def emit (s : State) (a : Action) (code : Nat) : State :=
  { s with outcomes := s.outcomes ++ [⟨a.name, code⟩] }

def insert (s : State) (a : Action) : State :=
  { s with environment := s.environment ++ [a.name],
           outcomes := s.outcomes ++ [⟨a.name, 0⟩] }

def halt (s : State) : State := { s with halted := true }

def step (s : State) (a : Action) : State :=
  if s.halted = true then s
  else if a.name ∈ s.environment then emit s a 3
  else match a.kind with
    | .good => insert s a
    | .mismatch => emit s a 6
    | .alias => if a.target ∈ s.environment then insert s a else emit s a 2
    | .scope => halt s

def run : State → List Action → State
  | s, [] => s
  | s, a :: rest => run (step s a) rest

def receipt (s : State) : Option Receipt :=
  if s.halted = true then none
  else some ⟨s.outcomes, s.environment.length, s.acceptanceAuthority⟩

def successfulNames : List Observation → List Nat
  | [] => []
  | observation :: rest =>
    if observation.code = 0 then observation.name :: successfulNames rest
    else successfulNames rest

def successfulCount (outcomes : List Observation) : Nat :=
  (successfulNames outcomes).length

def Invariant (s : State) : Prop :=
  s.environment = successfulNames s.outcomes ∧ s.environment.Nodup

/- Small constructive list lemmas keep the required theorem dependency closure
free of axioms. No imported list simplifier or quotient-based lemma is needed. -/
theorem append_nil_exact {α : Type} (xs : List α) : xs ++ [] = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (List.cons x) ih

theorem append_assoc_exact {α : Type} (xs ys zs : List α) :
    (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (List.cons x) ih

theorem mem_append_cases {α : Type} (x : α) (xs ys : List α)
    (h : x ∈ xs ++ ys) : x ∈ xs ∨ x ∈ ys := by
  induction xs with
  | nil => exact Or.inr h
  | cons y ys' ih =>
    cases h with
    | head => exact Or.inl (List.Mem.head _)
    | tail _ tail =>
      cases ih tail with
      | inl left => exact Or.inl (List.Mem.tail y left)
      | inr right => exact Or.inr right

theorem nodup_append_fresh (xs : List Nat) (name : Nat)
    (unique : xs.Nodup) (fresh : name ∉ xs) : (xs ++ [name]).Nodup := by
  induction unique with
  | nil => exact List.Pairwise.cons (fun _ member => nomatch member) List.Pairwise.nil
  | @cons head tail different unique ih =>
    apply List.Pairwise.cons
    · intro other member
      cases mem_append_cases other tail [name] member with
      | inl old => exact different other old
      | inr last =>
        cases last with
        | head =>
          intro equal
          apply fresh
          rw [← equal]
          exact List.Mem.head _
        | tail _ impossible => cases impossible
    · exact ih (fun member => fresh (List.Mem.tail head member))

theorem successfulNames_append (left right : List Observation) :
    successfulNames (left ++ right) = successfulNames left ++ successfulNames right := by
  induction left with
  | nil => rfl
  | cons observation rest ih =>
    change (if observation.code = 0 then observation.name :: successfulNames (rest ++ right)
            else successfulNames (rest ++ right)) =
      (if observation.code = 0 then observation.name :: successfulNames rest
       else successfulNames rest) ++ successfulNames right
    by_cases good : observation.code = 0
    · rw [ite_eq_left good, ite_eq_left good]
      exact congrArg (List.cons observation.name) ih
    · rw [ite_eq_right good, ite_eq_right good]
      exact ih

theorem successfulNames_emit (s : State) (a : Action) (code : Nat) (refused : code ≠ 0) :
    successfulNames (emit s a code).outcomes = successfulNames s.outcomes := by
  change successfulNames (s.outcomes ++ [⟨a.name, code⟩]) = successfulNames s.outcomes
  rw [successfulNames_append]
  change successfulNames s.outcomes ++ (if code = 0 then [a.name] else []) = _
  rw [ite_eq_right refused]
  exact append_nil_exact _

theorem successfulNames_insert (s : State) (a : Action) :
    successfulNames (insert s a).outcomes = successfulNames s.outcomes ++ [a.name] := by
  change successfulNames (s.outcomes ++ [⟨a.name, 0⟩]) = _
  rw [successfulNames_append]
  rfl

theorem emit_preserves_invariant (s : State) (a : Action) (code : Nat)
    (refused : code ≠ 0) (safe : Invariant s) : Invariant (emit s a code) := by
  constructor
  · change s.environment = successfulNames (emit s a code).outcomes
    rw [successfulNames_emit s a code refused]
    exact safe.1
  · exact safe.2

theorem insert_preserves_invariant (s : State) (a : Action)
    (fresh : a.name ∉ s.environment) (safe : Invariant s) : Invariant (insert s a) := by
  constructor
  · change s.environment ++ [a.name] = successfulNames (insert s a).outcomes
    rw [successfulNames_insert, safe.1]
  · exact nodup_append_fresh s.environment a.name safe.2 fresh

theorem initial_invariant : Invariant initial := ⟨rfl, List.Pairwise.nil⟩

theorem step_preserves_invariant (s : State) (a : Action)
    (safe : Invariant s) : Invariant (step s a) := by
  unfold step
  split
  · exact safe
  · split
    · exact emit_preserves_invariant s a 3 (by intro h; cases h) safe
    · rename_i fresh
      cases a.kind with
      | good => exact insert_preserves_invariant s a fresh safe
      | mismatch => exact emit_preserves_invariant s a 6 (by intro h; cases h) safe
      | alias =>
        change Invariant (if a.target ∈ s.environment then insert s a else emit s a 2)
        split
        · exact insert_preserves_invariant s a fresh safe
        · exact emit_preserves_invariant s a 2 (by intro h; cases h) safe
      | scope => exact safe

theorem run_preserves_invariant (s : State) (actions : List Action)
    (safe : Invariant s) : Invariant (run s actions) := by
  induction actions generalizing s with
  | nil => exact safe
  | cons a rest ih => exact ih (step s a) (step_preserves_invariant s a safe)

theorem run_environment_exact (actions : List Action) :
    (run initial actions).environment = successfulNames (run initial actions).outcomes :=
  (run_preserves_invariant initial actions initial_invariant).1

theorem run_environment_unique (actions : List Action) :
    (run initial actions).environment.Nodup :=
  (run_preserves_invariant initial actions initial_invariant).2

theorem run_success_count_exact (actions : List Action) :
    (run initial actions).environment.length = successfulCount (run initial actions).outcomes :=
  congrArg List.length (run_environment_exact actions)

theorem halted_step_identity (s : State) (a : Action) (stopped : s.halted = true) :
    step s a = s := by
  rw [step, ite_eq_left stopped]

theorem halted_run_identity (s : State) (actions : List Action) (stopped : s.halted = true) :
    run s actions = s := by
  induction actions with
  | nil => rfl
  | cons a rest ih =>
    change run (step s a) rest = s
    rw [halted_step_identity s a stopped]
    exact ih

theorem halted_no_receipt (s : State) (stopped : s.halted = true) : receipt s = none := by
  rw [receipt, ite_eq_left stopped]

theorem duplicate_precedes_checks (s : State) (a : Action)
    (running : s.halted ≠ true) (duplicate : a.name ∈ s.environment) :
    step s a = emit s a 3 := by
  rw [step, ite_eq_right running, ite_eq_left duplicate]

theorem duplicate_preserves_environment (s : State) (a : Action)
    (running : s.halted ≠ true) (duplicate : a.name ∈ s.environment) :
    (step s a).environment = s.environment := by
  rw [duplicate_precedes_checks s a running duplicate]
  rfl

theorem mismatch_preserves_environment (s : State) (name target : Nat)
    (running : s.halted ≠ true) :
    (step s ⟨.mismatch, name, target⟩).environment = s.environment := by
  unfold step
  rw [ite_eq_right running]
  split <;> rfl

theorem missing_alias_preserves_environment (s : State) (name target : Nat)
    (running : s.halted ≠ true) (missing : target ∉ s.environment) :
    (step s ⟨.alias, name, target⟩).environment = s.environment := by
  rw [step, ite_eq_right running]
  by_cases duplicate : name ∈ s.environment
  · rw [ite_eq_left duplicate]
    rfl
  · rw [ite_eq_right duplicate]
    change (if target ∈ s.environment then insert s ⟨.alias, name, target⟩
             else emit s ⟨.alias, name, target⟩ 2).environment = s.environment
    rw [ite_eq_right missing]
    rfl

theorem fresh_good_appends (s : State) (name target : Nat)
    (running : s.halted ≠ true) (fresh : name ∉ s.environment) :
    step s ⟨.good, name, target⟩ = insert s ⟨.good, name, target⟩ := by
  rw [step, ite_eq_right running, ite_eq_right fresh]

theorem fresh_scope_halts (s : State) (name target : Nat)
    (running : s.halted ≠ true) (fresh : name ∉ s.environment) :
    step s ⟨.scope, name, target⟩ = halt s := by
  rw [step, ite_eq_right running, ite_eq_right fresh]

theorem mismatch_then_retry_succeeds (s : State) (name : Nat)
    (running : s.halted ≠ true) (fresh : name ∉ s.environment) :
    (run s [⟨.mismatch, name, 0⟩, ⟨.good, name, 0⟩]).environment =
      s.environment ++ [name] := by
  change (step (step s ⟨.mismatch, name, 0⟩) ⟨.good, name, 0⟩).environment = _
  have refused : step s ⟨.mismatch, name, 0⟩ = emit s ⟨.mismatch, name, 0⟩ 6 := by
    rw [step, ite_eq_right running, ite_eq_right fresh]
  rw [refused, fresh_good_appends (emit s ⟨.mismatch, name, 0⟩ 6) name 0 running fresh]
  rfl

theorem step_preserves_authority (s : State) (a : Action) :
    (step s a).acceptanceAuthority = s.acceptanceAuthority := by
  unfold step
  split
  · rfl
  · split
    · rfl
    · cases a.kind with
      | good => rfl
      | mismatch => rfl
      | alias =>
        change (if a.target ∈ s.environment then insert s a else emit s a 2).acceptanceAuthority = _
        split <;> rfl
      | scope => rfl

theorem run_preserves_authority (s : State) (actions : List Action) :
    (run s actions).acceptanceAuthority = s.acceptanceAuthority := by
  induction actions generalizing s with
  | nil => rfl
  | cons a rest ih => exact (ih (step s a)).trans (step_preserves_authority s a)

theorem run_has_no_authority (actions : List Action) :
    (run initial actions).acceptanceAuthority = false :=
  run_preserves_authority initial actions

theorem completed_receipt_has_no_authority (actions : List Action) (result : Receipt)
    (completed : receipt (run initial actions) = some result) :
    result.acceptanceAuthority = false := by
  unfold receipt at completed
  split at completed
  · cases completed
  · cases completed
    exact run_has_no_authority actions

theorem step_environment_extends (s : State) (a : Action) :
    ∃ tail, (step s a).environment = s.environment ++ tail := by
  by_cases stopped : s.halted = true
  · refine ⟨[], ?_⟩
    rw [halted_step_identity s a stopped]
    exact (append_nil_exact _).symm
  · by_cases duplicate : a.name ∈ s.environment
    · refine ⟨[], ?_⟩
      rw [duplicate_preserves_environment s a stopped duplicate]
      exact (append_nil_exact _).symm
    · cases a with
      | mk kind name target =>
        cases kind with
        | good =>
          refine ⟨[name], ?_⟩
          rw [fresh_good_appends s name target stopped duplicate]
          rfl
        | mismatch =>
          refine ⟨[], ?_⟩
          rw [mismatch_preserves_environment s name target stopped]
          exact (append_nil_exact _).symm
        | alias =>
          by_cases present : target ∈ s.environment
          · refine ⟨[name], ?_⟩
            rw [step, ite_eq_right stopped, ite_eq_right duplicate]
            change (if target ∈ s.environment then insert s ⟨.alias, name, target⟩
                     else emit s ⟨.alias, name, target⟩ 2).environment = _
            rw [ite_eq_left present]
            rfl
          · refine ⟨[], ?_⟩
            rw [missing_alias_preserves_environment s name target stopped present]
            exact (append_nil_exact _).symm
        | scope =>
          refine ⟨[], ?_⟩
          rw [fresh_scope_halts s name target stopped duplicate]
          exact (append_nil_exact _).symm

theorem run_environment_extends (s : State) (actions : List Action) :
    ∃ tail, (run s actions).environment = s.environment ++ tail := by
  induction actions generalizing s with
  | nil => exact ⟨[], (append_nil_exact _).symm⟩
  | cons a rest ih =>
    obtain ⟨first, first_eq⟩ := step_environment_extends s a
    obtain ⟨later, later_eq⟩ := ih (step s a)
    exact ⟨first ++ later, later_eq.trans ((congrArg (fun xs => xs ++ later) first_eq).trans
      (append_assoc_exact s.environment first later))⟩

end GooseTransactions

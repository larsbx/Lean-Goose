import DefinitionTransactions

/-!
Stored binding records for the bounded definition-transaction profile.

Payload vectors are structural expression observations: Sort l = [0,l] and
Const n = [2,n]. Preservation results quantify over arbitrary existing vectors;
no typing, normalization, parser, cache, compiler, or general refinement theorem
is asserted. Lookup selects the most recently appended matching name even in an
arbitrary starting environment that contains duplicates.
-/
namespace GooseStoredBindings
open GooseTransactions (Kind Observation successfulNames successfulCount
  append_nil_exact append_assoc_exact nodup_append_fresh successfulNames_append)

structure Action where
  kind : Kind
  name : Nat
  target : Nat
  level : Nat
  deriving Repr

structure Binding where
  name : Nat
  type : List Nat
  value : List Nat
  inferred : List Nat
  deriving Repr

structure Snapshot where
  name : Nat
  code : Nat
  environment : List Binding
  deriving Repr

structure State where
  environment : List Binding
  outcomes : List Observation
  halted : Bool
  acceptanceAuthority : Bool
  snapshots : List Snapshot
  deriving Repr

structure Receipt where
  outcomes : List Observation
  successes : Nat
  acceptanceAuthority : Bool
  deriving Repr

def payloadDecidable : (left right : List Nat) → Decidable (left = right)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (fun equal => nomatch equal)
  | _ :: _, [] => isFalse (fun equal => nomatch equal)
  | x :: xs, y :: ys =>
    match Nat.decEq x y with
    | isFalse different => isFalse (fun equal => by cases equal; exact different rfl)
    | isTrue heads =>
      match payloadDecidable xs ys with
      | isFalse different => isFalse (fun equal => by cases equal; exact different rfl)
      | isTrue tails => isTrue (by cases heads; cases tails; rfl)

local instance payloadEquality (left right : List Nat) : Decidable (left = right) :=
  payloadDecidable left right

local instance nameMembership (name : Nat) (xs : List Nat) : Decidable (name ∈ xs) :=
  GooseTransactions.memberDecidable name xs

def names : List Binding → List Nat
  | [] => []
  | b :: rest => b.name :: names rest

def lookupFrom (name : Nat) : Option Binding → List Binding → Option Binding
  | previous, [] => previous
  | previous, b :: rest =>
    lookupFrom name (if name = b.name then some b else previous) rest

def lookup (name : Nat) (environment : List Binding) : Option Binding :=
  lookupFrom name none environment

def bindingAt : List Binding → Nat → Option Binding
  | [], _ => none
  | b :: _, 0 => some b
  | _ :: rest, index + 1 => bindingAt rest index

def initial : State := ⟨[], [], false, false, []⟩
def desiredType (a : Action) : List Nat := [0, a.level + 1]
def goodBinding (a : Action) : Binding :=
  ⟨a.name, desiredType a, [0, a.level], desiredType a⟩
def aliasBinding (a : Action) (target : Binding) : Binding :=
  ⟨a.name, desiredType a, [2, a.target], target.type⟩

def emit (s : State) (a : Action) (code : Nat) : State :=
  { s with outcomes := s.outcomes ++ [⟨a.name, code⟩],
           snapshots := s.snapshots ++ [⟨a.name, code, s.environment⟩] }

def insert (s : State) (a : Action) (b : Binding) : State :=
  { s with environment := s.environment ++ [b],
           outcomes := s.outcomes ++ [⟨a.name, 0⟩],
           snapshots := s.snapshots ++ [⟨a.name, 0, s.environment ++ [b]⟩] }

def halt (s : State) (a : Action) : State :=
  { s with halted := true,
           snapshots := s.snapshots ++ [⟨a.name, 1, s.environment⟩] }

def step (s : State) (a : Action) : State :=
  if s.halted = true then s
  else if a.name ∈ names s.environment then emit s a 3
  else match a.kind with
    | .good => insert s a (goodBinding a)
    | .mismatch => emit s a 6
    | .alias => match lookup a.target s.environment with
      | none => emit s a 2
      | some target =>
        if target.type = desiredType a then insert s a (aliasBinding a target)
        else emit s a 6
    | .scope => halt s a

def run : State → List Action → State
  | s, [] => s
  | s, a :: rest => run (step s a) rest

def receipt (s : State) : Option Receipt :=
  if s.halted = true then none
  else some ⟨s.outcomes, s.environment.length, s.acceptanceAuthority⟩

def Invariant (s : State) : Prop :=
  names s.environment = successfulNames s.outcomes ∧ (names s.environment).Nodup

theorem names_append (left right : List Binding) :
    names (left ++ right) = names left ++ names right := by
  induction left with
  | nil => rfl
  | cons b rest ih => exact congrArg (List.cons b.name) ih

theorem names_length (environment : List Binding) :
    (names environment).length = environment.length := by
  induction environment with
  | nil => rfl
  | cons b rest ih => exact congrArg Nat.succ ih

theorem mem_append_left {α : Type} (name : α) (left right : List α)
    (member : name ∈ left) : name ∈ left ++ right := by
  induction member with
  | head => exact List.Mem.head _
  | tail head _ ih => exact List.Mem.tail head ih

theorem lookupFrom_append (name : Nat) (previous : Option Binding)
    (left right : List Binding) :
    lookupFrom name previous (left ++ right) =
      lookupFrom name (lookupFrom name previous left) right := by
  induction left generalizing previous with
  | nil => rfl
  | cons b rest ih =>
    exact ih (if name = b.name then some b else previous)

theorem lookup_snoc (name : Nat) (environment : List Binding) (b : Binding) :
    lookup name (environment ++ [b]) =
      if name = b.name then some b else lookup name environment := by
  exact lookupFrom_append name none environment [b]

theorem lookup_latest_binding (environment : List Binding) (b : Binding) :
    lookup b.name (environment ++ [b]) = some b := by
  rw [lookup_snoc, ite_eq_left rfl]

theorem lookup_append_fresh_preserves_existing (environment : List Binding)
    (b : Binding) (name : Nat) (existing : name ∈ names environment)
    (fresh : b.name ∉ names environment) :
    lookup name (environment ++ [b]) = lookup name environment := by
  have different : name ≠ b.name := fun equal => fresh (equal ▸ existing)
  rw [lookup_snoc, ite_eq_right different]

theorem bindingAt_append_preserves (environment tail : List Binding) (index : Nat)
    (b : Binding) (existing : bindingAt environment index = some b) :
    bindingAt (environment ++ tail) index = some b := by
  induction environment generalizing index with
  | nil => cases existing
  | cons head rest ih =>
    cases index with
    | zero => exact existing
    | succ index => exact ih index existing

theorem halted_step_identity (s : State) (a : Action) (stopped : s.halted = true) :
    step s a = s := by rw [step, ite_eq_left stopped]

theorem duplicate_precedes_checks (s : State) (a : Action)
    (running : s.halted ≠ true) (duplicate : a.name ∈ names s.environment) :
    step s a = emit s a 3 := by
  rw [step, ite_eq_right running, ite_eq_left duplicate]

theorem fresh_good_payload_exact (s : State) (name target level : Nat)
    (running : s.halted ≠ true) (fresh : name ∉ names s.environment) :
    step s ⟨.good, name, target, level⟩ =
      insert s ⟨.good, name, target, level⟩
        ⟨name, [0, level + 1], [0, level], [0, level + 1]⟩ := by
  rw [step, ite_eq_right running, ite_eq_right fresh]
  rfl

theorem fresh_alias_payload_exact (s : State) (name target level : Nat) (b : Binding)
    (running : s.halted ≠ true) (fresh : name ∉ names s.environment)
    (found : lookup target s.environment = some b) (typed : b.type = [0, level + 1]) :
    step s ⟨.alias, name, target, level⟩ =
      insert s ⟨.alias, name, target, level⟩ ⟨name, [0, level + 1], [2, target], b.type⟩ := by
  rw [step, ite_eq_right running, ite_eq_right fresh]
  change (match lookup target s.environment with
    | none => emit s ⟨.alias, name, target, level⟩ 2
    | some value => if value.type = [0, level + 1]
        then insert s ⟨.alias, name, target, level⟩ (aliasBinding ⟨.alias, name, target, level⟩ value)
        else emit s ⟨.alias, name, target, level⟩ 6) = _
  rw [found]
  dsimp only
  rw [ite_eq_left typed]
  rfl

/-- Every step preserves the environment or appends one fresh, named record. -/
theorem step_shape (s : State) (a : Action) :
    step s a = s ∨
    (∃ code, code ≠ 0 ∧ step s a = emit s a code) ∨
    (∃ b, b.name = a.name ∧ a.name ∉ names s.environment ∧ step s a = insert s a b) ∨
    step s a = halt s a := by
  by_cases stopped : s.halted = true
  · exact Or.inl (halted_step_identity s a stopped)
  · by_cases duplicate : a.name ∈ names s.environment
    · exact Or.inr (Or.inl ⟨3, (by intro h; cases h), duplicate_precedes_checks s a stopped duplicate⟩)
    · cases a with
      | mk kind name target level =>
        cases kind with
        | good =>
          exact Or.inr (Or.inr (Or.inl ⟨goodBinding ⟨.good, name, target, level⟩,
            rfl, duplicate, fresh_good_payload_exact s name target level stopped duplicate⟩))
        | mismatch =>
          refine Or.inr (Or.inl ⟨6, (by intro h; cases h), ?_⟩)
          rw [step, ite_eq_right stopped, ite_eq_right duplicate]
        | scope =>
          apply Or.inr; apply Or.inr; apply Or.inr
          rw [step, ite_eq_right stopped, ite_eq_right duplicate]
        | alias =>
          cases found : lookup target s.environment with
          | none =>
            refine Or.inr (Or.inl ⟨2, (by intro h; cases h), ?_⟩)
            rw [step, ite_eq_right stopped, ite_eq_right duplicate]
            change (match lookup target s.environment with
              | none => emit s ⟨.alias, name, target, level⟩ 2
              | some b => if b.type = desiredType ⟨.alias, name, target, level⟩
                  then insert s ⟨.alias, name, target, level⟩ (aliasBinding ⟨.alias, name, target, level⟩ b)
                  else emit s ⟨.alias, name, target, level⟩ 6) = _
            rw [found]
          | some b =>
            by_cases typed : b.type = [0, level + 1]
            · exact Or.inr (Or.inr (Or.inl ⟨aliasBinding ⟨.alias, name, target, level⟩ b,
                rfl, duplicate, fresh_alias_payload_exact s name target level b stopped duplicate found typed⟩))
            · refine Or.inr (Or.inl ⟨6, (by intro h; cases h), ?_⟩)
              rw [step, ite_eq_right stopped, ite_eq_right duplicate]
              change (match lookup target s.environment with
                | none => emit s ⟨.alias, name, target, level⟩ 2
                | some value => if value.type = [0, level + 1]
                    then insert s ⟨.alias, name, target, level⟩ (aliasBinding ⟨.alias, name, target, level⟩ value)
                    else emit s ⟨.alias, name, target, level⟩ 6) = _
              rw [found]
              dsimp only
              rw [ite_eq_right typed]

theorem duplicate_preserves_environment (s : State) (a : Action)
    (running : s.halted ≠ true) (duplicate : a.name ∈ names s.environment) :
    (step s a).environment = s.environment := by
  rw [duplicate_precedes_checks s a running duplicate]
  rfl

theorem mismatch_preserves_environment (s : State) (name target level : Nat)
    (running : s.halted ≠ true) :
    (step s ⟨.mismatch, name, target, level⟩).environment = s.environment := by
  by_cases duplicate : name ∈ names s.environment
  · exact duplicate_preserves_environment s _ running duplicate
  · rw [step, ite_eq_right running, ite_eq_right duplicate]
    rfl

theorem missing_alias_preserves_environment (s : State) (name target level : Nat)
    (running : s.halted ≠ true) (missing : lookup target s.environment = none) :
    (step s ⟨.alias, name, target, level⟩).environment = s.environment := by
  by_cases duplicate : name ∈ names s.environment
  · exact duplicate_preserves_environment s _ running duplicate
  · rw [step, ite_eq_right running, ite_eq_right duplicate]
    change (match lookup target s.environment with
      | none => emit s ⟨.alias, name, target, level⟩ 2
      | some b => if b.type = [0, level + 1]
          then insert s ⟨.alias, name, target, level⟩ (aliasBinding ⟨.alias, name, target, level⟩ b)
          else emit s ⟨.alias, name, target, level⟩ 6).environment = _
    rw [missing]
    rfl

theorem wrong_type_alias_preserves_environment (s : State) (name target level : Nat)
    (b : Binding) (running : s.halted ≠ true) (found : lookup target s.environment = some b)
    (wrong : b.type ≠ [0, level + 1]) :
    (step s ⟨.alias, name, target, level⟩).environment = s.environment := by
  by_cases duplicate : name ∈ names s.environment
  · exact duplicate_preserves_environment s _ running duplicate
  · rw [step, ite_eq_right running, ite_eq_right duplicate]
    change (match lookup target s.environment with
      | none => emit s ⟨.alias, name, target, level⟩ 2
      | some value => if value.type = [0, level + 1]
          then insert s ⟨.alias, name, target, level⟩ (aliasBinding ⟨.alias, name, target, level⟩ value)
          else emit s ⟨.alias, name, target, level⟩ 6).environment = _
    rw [found]
    dsimp only
    rw [ite_eq_right wrong]
    rfl

theorem emit_preserves_invariant (s : State) (a : Action) (code : Nat)
    (refused : code ≠ 0) (safe : Invariant s) : Invariant (emit s a code) := by
  constructor
  · change names s.environment = successfulNames (s.outcomes ++ [⟨a.name, code⟩])
    rw [successfulNames_append]
    change names s.environment = successfulNames s.outcomes ++ (if code = 0 then [a.name] else [])
    rw [ite_eq_right refused, append_nil_exact]
    exact safe.1
  · exact safe.2

theorem insert_preserves_invariant (s : State) (a : Action) (b : Binding)
    (sameName : b.name = a.name) (fresh : a.name ∉ names s.environment)
    (safe : Invariant s) : Invariant (insert s a b) := by
  constructor
  · change names (s.environment ++ [b]) = successfulNames (s.outcomes ++ [⟨a.name, 0⟩])
    rw [names_append, successfulNames_append]
    change names s.environment ++ [b.name] = successfulNames s.outcomes ++ [a.name]
    rw [sameName, safe.1]
  · change (names (s.environment ++ [b])).Nodup
    rw [names_append]
    change (names s.environment ++ [b.name]).Nodup
    rw [sameName]
    exact nodup_append_fresh _ _ safe.2 fresh

theorem initial_invariant : Invariant initial := ⟨rfl, List.Pairwise.nil⟩

theorem step_preserves_invariant (s : State) (a : Action) (safe : Invariant s) :
    Invariant (step s a) := by
  rcases step_shape s a with unchanged | ⟨code, refused, emitted⟩ | ⟨b, sameName, fresh, inserted⟩ | stopped
  · rw [unchanged]; exact safe
  · rw [emitted]; exact emit_preserves_invariant s a code refused safe
  · rw [inserted]; exact insert_preserves_invariant s a b sameName fresh safe
  · rw [stopped]; exact safe

theorem run_preserves_invariant (s : State) (actions : List Action) (safe : Invariant s) :
    Invariant (run s actions) := by
  induction actions generalizing s with
  | nil => exact safe
  | cons a rest ih => exact ih (step s a) (step_preserves_invariant s a safe)

theorem run_success_names_exact (actions : List Action) :
    names (run initial actions).environment = successfulNames (run initial actions).outcomes :=
  (run_preserves_invariant initial actions initial_invariant).1

theorem run_environment_unique (actions : List Action) :
    (names (run initial actions).environment).Nodup :=
  (run_preserves_invariant initial actions initial_invariant).2

theorem run_success_count_exact (actions : List Action) :
    (run initial actions).environment.length = successfulCount (run initial actions).outcomes :=
  (names_length _).symm.trans (congrArg List.length (run_success_names_exact actions))

theorem step_environment_extends (s : State) (a : Action) :
    ∃ tail, (step s a).environment = s.environment ++ tail := by
  rcases step_shape s a with unchanged | ⟨code, _, emitted⟩ | ⟨b, _, _, inserted⟩ | stopped
  · refine ⟨[], ?_⟩; rw [unchanged]; exact (append_nil_exact _).symm
  · refine ⟨[], ?_⟩; rw [emitted]; exact (append_nil_exact _).symm
  · refine ⟨[b], ?_⟩; rw [inserted]; rfl
  · refine ⟨[], ?_⟩; rw [stopped]; exact (append_nil_exact _).symm

theorem run_environment_extends (s : State) (actions : List Action) :
    ∃ tail, (run s actions).environment = s.environment ++ tail := by
  induction actions generalizing s with
  | nil => exact ⟨[], (append_nil_exact _).symm⟩
  | cons a rest ih =>
    obtain ⟨first, first_eq⟩ := step_environment_extends s a
    obtain ⟨later, later_eq⟩ := ih (step s a)
    exact ⟨first ++ later, later_eq.trans ((congrArg (fun xs => xs ++ later) first_eq).trans
      (append_assoc_exact s.environment first later))⟩

theorem run_preserves_existing_binding (s : State) (actions : List Action)
    (index : Nat) (b : Binding) (existing : bindingAt s.environment index = some b) :
    bindingAt (run s actions).environment index = some b := by
  obtain ⟨tail, extension⟩ := run_environment_extends s actions
  rw [extension]
  exact bindingAt_append_preserves s.environment tail index b existing

/-- All three payloads remain exactly equal for every pre-existing indexed record. -/
theorem run_preserves_existing_binding_fields (s : State) (actions : List Action)
    (index : Nat) (b : Binding) (existing : bindingAt s.environment index = some b) :
    bindingAt (run s actions).environment index = some b ∧
    (bindingAt (run s actions).environment index).map Binding.type = some b.type ∧
    (bindingAt (run s actions).environment index).map Binding.value = some b.value ∧
    (bindingAt (run s actions).environment index).map Binding.inferred = some b.inferred := by
  have preserved := run_preserves_existing_binding s actions index b existing
  refine ⟨preserved, ?_, ?_, ?_⟩ <;> rw [preserved] <;> rfl

theorem step_preserves_existing_lookup (s : State) (a : Action) (name : Nat)
    (existing : name ∈ names s.environment) :
    lookup name (step s a).environment = lookup name s.environment := by
  rcases step_shape s a with unchanged | ⟨code, _, emitted⟩ | ⟨b, sameName, fresh, inserted⟩ | stopped
  · rw [unchanged]
  · rw [emitted]; rfl
  · rw [inserted]
    apply lookup_append_fresh_preserves_existing s.environment b name existing
    rw [sameName]
    exact fresh
  · rw [stopped]; rfl

theorem step_preserves_name_membership (s : State) (a : Action) (name : Nat)
    (existing : name ∈ names s.environment) : name ∈ names (step s a).environment := by
  obtain ⟨tail, extension⟩ := step_environment_extends s a
  rw [extension, names_append]
  exact mem_append_left name (names s.environment) (names tail) existing

theorem run_preserves_existing_lookup (s : State) (actions : List Action) (name : Nat)
    (existing : name ∈ names s.environment) :
    lookup name (run s actions).environment = lookup name s.environment := by
  induction actions generalizing s with
  | nil => rfl
  | cons a rest ih =>
    exact (ih (step s a) (step_preserves_name_membership s a name existing)).trans
      (step_preserves_existing_lookup s a name existing)

theorem step_preserves_name_uniqueness (s : State) (a : Action)
    (unique : (names s.environment).Nodup) : (names (step s a).environment).Nodup := by
  rcases step_shape s a with unchanged | ⟨code, _, emitted⟩ | ⟨b, sameName, fresh, inserted⟩ | stopped
  · rw [unchanged]; exact unique
  · rw [emitted]; exact unique
  · rw [inserted]
    change (names (s.environment ++ [b])).Nodup
    rw [names_append]
    change (names s.environment ++ [b.name]).Nodup
    rw [sameName]
    exact nodup_append_fresh _ _ unique fresh
  · rw [stopped]; exact unique

theorem run_preserves_name_uniqueness (s : State) (actions : List Action)
    (unique : (names s.environment).Nodup) : (names (run s actions).environment).Nodup := by
  induction actions generalizing s with
  | nil => exact unique
  | cons a rest ih => exact ih (step s a) (step_preserves_name_uniqueness s a unique)

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

theorem step_preserves_authority (s : State) (a : Action) :
    (step s a).acceptanceAuthority = s.acceptanceAuthority := by
  rcases step_shape s a with unchanged | ⟨code, _, emitted⟩ | ⟨b, _, _, inserted⟩ | stopped
  · rw [unchanged]
  · rw [emitted]; rfl
  · rw [inserted]; rfl
  · rw [stopped]; rfl

theorem run_preserves_authority (s : State) (actions : List Action) :
    (run s actions).acceptanceAuthority = s.acceptanceAuthority := by
  induction actions generalizing s with
  | nil => rfl
  | cons a rest ih => exact (ih (step s a)).trans (step_preserves_authority s a)

theorem run_has_no_authority (actions : List Action) :
    (run initial actions).acceptanceAuthority = false := run_preserves_authority initial actions

theorem completed_receipt_has_no_authority (actions : List Action) (result : Receipt)
    (completed : receipt (run initial actions) = some result) : result.acceptanceAuthority = false := by
  unfold receipt at completed
  split at completed
  · cases completed
  · cases completed
    exact run_has_no_authority actions

end GooseStoredBindings

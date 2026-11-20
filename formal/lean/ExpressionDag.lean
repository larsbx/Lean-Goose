import Init

/-!
Structural expression representation and scope for an ordered immutable DAG.

The decoder is unbounded and accepts precisely backward references. Names are
opaque lists of naturals; ASCII restrictions belong to the replay/native wire.
These statements do not formalize substitution, typing, conversion, resource
limits, parser correctness, or refinement of the Goose implementation.
-/
namespace GooseExpressionDag

inductive Expr where
  | sort (level : Nat)
  | var (index : Nat)
  | const (name : List Nat)
  | app (fn arg : Expr)
  | lam (domain body : Expr)
  | pi (domain codomain : Expr)
  | letE (type value body : Expr)
  deriving Repr

inductive RawNode where
  | sort (level : Nat)
  | var (index : Nat)
  | const (name : List Nat)
  | app (fn arg : Nat)
  | lam (domain body : Nat)
  | pi (domain codomain : Nat)
  | letE (type value body : Nat)
  deriving Repr

def lookup {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => lookup xs n

/- Exhaustive nested Option cases avoid a sparse-pattern compiler helper whose
bit-mask arithmetic proof would otherwise add propext to the decoder closure. -/
def binary (constructor : Expr → Expr → Expr) (left right : Option Expr) : Option Expr :=
  match left with
  | none => none
  | some a => match right with
      | none => none
      | some b => some (constructor a b)

def ternary (constructor : Expr → Expr → Expr → Expr)
    (first second third : Option Expr) : Option Expr :=
  match first with
  | none => none
  | some a => match second with
      | none => none
      | some b => match third with
          | none => none
          | some c => some (constructor a b c)

def decodeNode (table : List Expr) : RawNode → Option Expr
  | .sort level => some (.sort level)
  | .var index => some (.var index)
  | .const name => some (.const name)
  | .app fn arg => binary .app (lookup table fn) (lookup table arg)
  | .lam domain body => binary .lam (lookup table domain) (lookup table body)
  | .pi domain codomain => binary .pi (lookup table domain) (lookup table codomain)
  | .letE type value body => ternary .letE (lookup table type) (lookup table value) (lookup table body)

def decodeFrom (table : List Expr) (nodes : List RawNode) : Option (List Expr) :=
  match nodes with
  | [] => some table
  | node :: rest => match decodeNode table node with
      | none => none
      | some expression => decodeFrom (table ++ [expression]) rest
termination_by structural nodes

def decode (nodes : List RawNode) : Option (List Expr) := decodeFrom [] nodes

def NodeTopological (size : Nat) : RawNode → Prop
  | .sort _ | .var _ | .const _ => True
  | .app a b | .lam a b | .pi a b => a < size ∧ b < size
  | .letE a b c => a < size ∧ b < size ∧ c < size

def TopologicalFrom : Nat → List RawNode → Prop
  | _, [] => True
  | size, node :: rest => NodeTopological size node ∧ TopologicalFrom (size + 1) rest

def Topological (nodes : List RawNode) : Prop := TopologicalFrom 0 nodes

inductive RefersTo : RawNode → Nat → Prop where
  | appFn (a b) : RefersTo (.app a b) a
  | appArg (a b) : RefersTo (.app a b) b
  | lamDomain (a b) : RefersTo (.lam a b) a
  | lamBody (a b) : RefersTo (.lam a b) b
  | piDomain (a b) : RefersTo (.pi a b) a
  | piBody (a b) : RefersTo (.pi a b) b
  | letType (a b c) : RefersTo (.letE a b c) a
  | letValue (a b c) : RefersTo (.letE a b c) b
  | letBody (a b c) : RefersTo (.letE a b c) c

def Edge (nodes : List RawNode) (parent child : Nat) : Prop :=
  ∃ node, lookup nodes parent = some node ∧ RefersTo node child

/-- A nonempty directed path following raw child IDs. -/
inductive DagPath (nodes : List RawNode) : Nat → Nat → Prop where
  | edge {parent child} : Edge nodes parent child → DagPath nodes parent child
  | trans {a b c} : DagPath nodes a b → DagPath nodes b c → DagPath nodes a c

/-- Independent relational specification of one structural decoding step. -/
inductive RepresentsNode (table : List Expr) : RawNode → Expr → Prop where
  | sort (level) : RepresentsNode table (.sort level) (.sort level)
  | var (index) : RepresentsNode table (.var index) (.var index)
  | const (name) : RepresentsNode table (.const name) (.const name)
  | app {a b f x} : lookup table a = some f → lookup table b = some x →
      RepresentsNode table (.app a b) (.app f x)
  | lam {a b d e} : lookup table a = some d → lookup table b = some e →
      RepresentsNode table (.lam a b) (.lam d e)
  | pi {a b d e} : lookup table a = some d → lookup table b = some e →
      RepresentsNode table (.pi a b) (.pi d e)
  | letE {a b c t v e} : lookup table a = some t → lookup table b = some v → lookup table c = some e →
      RepresentsNode table (.letE a b c) (.letE t v e)

/-- A sequence of structural representations, in the original node order. -/
inductive RepresentsFrom : List Expr → List RawNode → List Expr → Prop where
  | nil (table) : RepresentsFrom table [] table
  | cons {table node expression rest result} : RepresentsNode table node expression →
      RepresentsFrom (table ++ [expression]) rest result →
      RepresentsFrom table (node :: rest) result

def Represents (nodes : List RawNode) (table : List Expr) : Prop := RepresentsFrom [] nodes table

def height : Expr → Nat
  | .sort _ | .var _ | .const _ => 1
  | .app a b | .lam a b | .pi a b => Nat.max (height a) (height b) + 1
  | .letE a b c => Nat.max (height a) (Nat.max (height b) (height c)) + 1

inductive DirectChild : Expr → Expr → Prop where
  | appFn (a b) : DirectChild a (.app a b)
  | appArg (a b) : DirectChild b (.app a b)
  | lamDomain (a b) : DirectChild a (.lam a b)
  | lamBody (a b) : DirectChild b (.lam a b)
  | piDomain (a b) : DirectChild a (.pi a b)
  | piBody (a b) : DirectChild b (.pi a b)
  | letType (a b c) : DirectChild a (.letE a b c)
  | letValue (a b c) : DirectChild b (.letE a b c)
  | letBody (a b c) : DirectChild c (.letE a b c)

/-- Number of ambient binders required for all variables to be in scope. -/
def loose : Expr → Nat
  | .sort _ | .const _ => 0
  | .var index => index + 1
  | .app a b => Nat.max (loose a) (loose b)
  | .lam a b | .pi a b => Nat.max (loose a) (loose b - 1)
  | .letE a b c => Nat.max (loose a) (Nat.max (loose b) (loose c - 1))

inductive Scoped : Nat → Expr → Prop where
  | sort (depth level) : Scoped depth (.sort level)
  | var {depth index} : index < depth → Scoped depth (.var index)
  | const (depth name) : Scoped depth (.const name)
  | app {depth a b} : Scoped depth a → Scoped depth b → Scoped depth (.app a b)
  | lam {depth a b} : Scoped depth a → Scoped (depth + 1) b → Scoped depth (.lam a b)
  | pi {depth a b} : Scoped depth a → Scoped (depth + 1) b → Scoped depth (.pi a b)
  | letE {depth a b c} : Scoped depth a → Scoped depth b → Scoped (depth + 1) c →
      Scoped depth (.letE a b c)

def Closed (expression : Expr) : Prop := Scoped 0 expression

def scopeCheck (expression : Expr) (depth : Nat) : Bool :=
  if loose expression ≤ depth then true else false

/-- Arity-delimited structural prefix wire, with explicit constant-name length. -/
def encode : Expr → List Nat
  | .sort level => [0, level]
  | .var index => [1, index]
  | .const name => [2, name.length] ++ name
  | .app a b => [3] ++ encode a ++ encode b
  | .lam a b => [4] ++ encode a ++ encode b
  | .pi a b => [5] ++ encode a ++ encode b
  | .letE a b c => [6] ++ encode a ++ encode b ++ encode c

structure Projection where
  decoded : Bool
  expressions : List (List Nat)
  heights : List Nat
  loose : List Nat
  scopeResults : List (List Bool)
  acceptanceAuthority : Bool
  deriving Repr

def observe (nodes : List RawNode) (depths : List Nat) : Projection :=
  match decode nodes with
  | none => ⟨false, [], [], [], [], false⟩
  | some table => ⟨true, table.map encode, table.map height, table.map loose,
      table.map (fun e => depths.map (scopeCheck e)), false⟩

/- Constructive list helpers avoid quotient/extensionality axioms in proofs. -/
theorem append_nil_exact {α : Type} (xs : List α) : xs ++ [] = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (List.cons x) ih

theorem append_assoc_exact {α : Type} (xs ys zs : List α) :
    (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (List.cons x) ih

theorem length_append_exact {α : Type} (xs ys : List α) :
    (xs ++ ys).length = xs.length + ys.length := by
  induction xs with
  | nil => exact (Nat.zero_add _).symm
  | cons x xs ih =>
    change (xs ++ ys).length + 1 = (xs.length + 1) + ys.length
    rw [ih, Nat.add_right_comm]

theorem at_some_lt {α : Type} (xs : List α) (index : Nat) (value : α)
    (found : lookup xs index = some value) : index < xs.length := by
  induction xs generalizing index with
  | nil => cases found
  | cons head tail ih =>
    cases index with
    | zero => exact Nat.zero_lt_succ _
    | succ index => exact Nat.succ_lt_succ (ih index found)

theorem at_exists_of_lt {α : Type} (xs : List α) (index : Nat)
    (inside : index < xs.length) : ∃ value, lookup xs index = some value := by
  induction xs generalizing index with
  | nil => exact False.elim (Nat.not_lt_zero _ inside)
  | cons head tail ih =>
    cases index with
    | zero => exact ⟨head, rfl⟩
    | succ index => exact ih index (Nat.lt_of_succ_lt_succ inside)

theorem at_append_preserves {α : Type} (xs ys : List α) (index : Nat) (value : α)
    (found : lookup xs index = some value) : lookup (xs ++ ys) index = some value := by
  induction xs generalizing index with
  | nil => cases found
  | cons head tail ih =>
    cases index with
    | zero => exact found
    | succ index => exact ih index found

theorem at_append_last {α : Type} (xs : List α) (value : α) :
    lookup (xs ++ [value]) xs.length = some value := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem at_none_of_ge {α : Type} (xs : List α) (index : Nat)
    (outside : xs.length ≤ index) : lookup xs index = none := by
  induction xs generalizing index with
  | nil => rfl
  | cons head tail ih =>
    cases index with
    | zero => exact False.elim (Nat.not_succ_le_zero _ outside)
    | succ index => exact ih index (Nat.le_of_succ_le_succ outside)

theorem decodeNode_sound (table : List Expr) (node : RawNode) (expression : Expr)
    (decoded : decodeNode table node = some expression) : RepresentsNode table node expression := by
  cases node with
  | sort level => cases decoded; exact RepresentsNode.sort level
  | var index => cases decoded; exact RepresentsNode.var index
  | const name => cases decoded; exact RepresentsNode.const name
  | app a b =>
    dsimp only [decodeNode] at decoded
    cases ha : lookup table a with
    | none => rw [ha] at decoded; cases decoded
    | some first =>
      rw [ha] at decoded
      cases hb : lookup table b with
      | none => rw [hb] at decoded; cases decoded
      | some second =>
        rw [hb] at decoded
        cases decoded
        exact RepresentsNode.app ha hb
  | lam a b =>
    dsimp only [decodeNode] at decoded
    cases ha : lookup table a with
    | none => rw [ha] at decoded; cases decoded
    | some first =>
      rw [ha] at decoded
      cases hb : lookup table b with
      | none => rw [hb] at decoded; cases decoded
      | some second =>
        rw [hb] at decoded
        cases decoded
        exact RepresentsNode.lam ha hb
  | pi a b =>
    dsimp only [decodeNode] at decoded
    cases ha : lookup table a with
    | none => rw [ha] at decoded; cases decoded
    | some first =>
      rw [ha] at decoded
      cases hb : lookup table b with
      | none => rw [hb] at decoded; cases decoded
      | some second =>
        rw [hb] at decoded
        cases decoded
        exact RepresentsNode.pi ha hb
  | letE a b c =>
    dsimp only [decodeNode] at decoded
    cases ha : lookup table a with
    | none => rw [ha] at decoded; cases decoded
    | some first =>
      rw [ha] at decoded
      cases hb : lookup table b with
      | none => rw [hb] at decoded; cases decoded
      | some second =>
        rw [hb] at decoded
        cases hc : lookup table c with
        | none => rw [hc] at decoded; cases decoded
        | some third =>
          rw [hc] at decoded
          cases decoded
          exact RepresentsNode.letE ha hb hc

theorem decodeNode_complete {table : List Expr} {node : RawNode} {expression : Expr}
    (represented : RepresentsNode table node expression) : decodeNode table node = some expression := by
  cases represented with
  | sort => rfl
  | var => rfl
  | const => rfl
  | app ha hb => dsimp only [decodeNode]; rw [ha, hb]; rfl
  | lam ha hb => dsimp only [decodeNode]; rw [ha, hb]; rfl
  | pi ha hb => dsimp only [decodeNode]; rw [ha, hb]; rfl
  | letE ha hb hc => dsimp only [decodeNode]; rw [ha, hb, hc]; rfl

theorem representsNode_topological {table : List Expr} {node : RawNode} {expression : Expr}
    (represented : RepresentsNode table node expression) : NodeTopological table.length node := by
  cases represented with
  | sort => trivial
  | var => trivial
  | const => trivial
  | app ha hb => exact ⟨at_some_lt _ _ _ ha, at_some_lt _ _ _ hb⟩
  | lam ha hb => exact ⟨at_some_lt _ _ _ ha, at_some_lt _ _ _ hb⟩
  | pi ha hb => exact ⟨at_some_lt _ _ _ ha, at_some_lt _ _ _ hb⟩
  | letE ha hb hc => exact ⟨at_some_lt _ _ _ ha, at_some_lt _ _ _ hb, at_some_lt _ _ _ hc⟩

theorem topologicalNode_complete (table : List Expr) (node : RawNode)
    (valid : NodeTopological table.length node) : ∃ expression, decodeNode table node = some expression := by
  cases node with
  | sort level => exact ⟨.sort level, rfl⟩
  | var index => exact ⟨.var index, rfl⟩
  | const name => exact ⟨.const name, rfl⟩
  | app a b =>
    obtain ⟨first, ha⟩ := at_exists_of_lt table a valid.1
    obtain ⟨second, hb⟩ := at_exists_of_lt table b valid.2
    exact ⟨.app first second, decodeNode_complete (RepresentsNode.app ha hb)⟩
  | lam a b =>
    obtain ⟨first, ha⟩ := at_exists_of_lt table a valid.1
    obtain ⟨second, hb⟩ := at_exists_of_lt table b valid.2
    exact ⟨.lam first second, decodeNode_complete (RepresentsNode.lam ha hb)⟩
  | pi a b =>
    obtain ⟨first, ha⟩ := at_exists_of_lt table a valid.1
    obtain ⟨second, hb⟩ := at_exists_of_lt table b valid.2
    exact ⟨.pi first second, decodeNode_complete (RepresentsNode.pi ha hb)⟩
  | letE a b c =>
    obtain ⟨first, ha⟩ := at_exists_of_lt table a valid.1
    obtain ⟨second, hb⟩ := at_exists_of_lt table b valid.2.1
    obtain ⟨third, hc⟩ := at_exists_of_lt table c valid.2.2
    exact ⟨.letE first second third, decodeNode_complete (RepresentsNode.letE ha hb hc)⟩

theorem decodeNode_success_iff_topological (table : List Expr) (node : RawNode) :
    (∃ expression, decodeNode table node = some expression) ↔ NodeTopological table.length node := by
  constructor
  · intro h
    obtain ⟨expression, decoded⟩ := h
    exact representsNode_topological (decodeNode_sound table node expression decoded)
  · exact topologicalNode_complete table node

theorem decodeFrom_sound (table : List Expr) (nodes : List RawNode) (result : List Expr)
    (decoded : decodeFrom table nodes = some result) : RepresentsFrom table nodes result := by
  induction nodes generalizing table result with
  | nil => cases decoded; exact RepresentsFrom.nil table
  | cons node rest ih =>
    cases first : decodeNode table node with
    | none => rw [decodeFrom, first] at decoded; cases decoded
    | some expression =>
      rw [decodeFrom, first] at decoded
      exact RepresentsFrom.cons (decodeNode_sound _ _ _ first) (ih _ _ decoded)

theorem decodeFrom_complete {table : List Expr} {nodes : List RawNode} {result : List Expr}
    (represented : RepresentsFrom table nodes result) : decodeFrom table nodes = some result := by
  induction represented with
  | nil => rfl
  | cons node rest ih =>
    rw [decodeFrom, decodeNode_complete node]
    exact ih

theorem representsFrom_length {table : List Expr} {nodes : List RawNode} {result : List Expr}
    (represented : RepresentsFrom table nodes result) : result.length = table.length + nodes.length := by
  induction represented with
  | nil => rfl
  | @cons table node expression rest result first remaining ih =>
    rw [ih, length_append_exact]
    exact Nat.add_right_comm _ _ _

theorem representsFrom_topological {table : List Expr} {nodes : List RawNode} {result : List Expr}
    (represented : RepresentsFrom table nodes result) : TopologicalFrom table.length nodes := by
  induction represented with
  | nil => trivial
  | cons first rest ih =>
    constructor
    · exact representsNode_topological first
    · rw [length_append_exact] at ih
      exact ih

theorem topologicalFrom_complete (table : List Expr) (nodes : List RawNode)
    (valid : TopologicalFrom table.length nodes) : ∃ result, decodeFrom table nodes = some result := by
  induction nodes generalizing table with
  | nil => exact ⟨table, rfl⟩
  | cons node rest ih =>
    obtain ⟨expression, first⟩ := topologicalNode_complete table node valid.1
    have tailValid : TopologicalFrom (table ++ [expression]).length rest := by
      rw [length_append_exact]
      exact valid.2
    obtain ⟨result, tailDecoded⟩ := ih (table ++ [expression]) tailValid
    refine ⟨result, ?_⟩
    rw [decodeFrom, first]
    exact tailDecoded

theorem decode_sound (nodes : List RawNode) (table : List Expr)
    (decoded : decode nodes = some table) : Represents nodes table :=
  decodeFrom_sound [] nodes table decoded

theorem decode_complete (nodes : List RawNode) (table : List Expr)
    (represented : Represents nodes table) : decode nodes = some table :=
  decodeFrom_complete represented

theorem decode_length (nodes : List RawNode) (table : List Expr)
    (decoded : decode nodes = some table) : table.length = nodes.length := by
  have exactLength := representsFrom_length (decode_sound nodes table decoded)
  exact (exactLength.trans (Nat.zero_add _))

theorem decode_success_iff_topological (nodes : List RawNode) :
    (∃ table, decode nodes = some table) ↔ Topological nodes := by
  constructor
  · intro h
    obtain ⟨table, decoded⟩ := h
    exact representsFrom_topological (decode_sound nodes table decoded)
  · exact topologicalFrom_complete [] nodes

theorem decode_rejects_non_topological (nodes : List RawNode) (invalid : ¬ Topological nodes) :
    decode nodes = none := by
  cases result : decode nodes with
  | none => rfl
  | some table => exact False.elim (invalid ((decode_success_iff_topological nodes).1 ⟨table, result⟩))

theorem topologicalFrom_lookup (size : Nat) (nodes : List RawNode) (index : Nat) (node : RawNode)
    (valid : TopologicalFrom size nodes) (found : lookup nodes index = some node) :
    NodeTopological (size + index) node := by
  induction nodes generalizing size index with
  | nil => cases found
  | cons head tail ih =>
    cases index with
    | zero =>
      change some head = some node at found
      cases found
      exact valid.1
    | succ index =>
      have result := ih (size + 1) index valid.2 found
      rw [Nat.add_right_comm] at result
      exact result

theorem references_point_backwards (size : Nat) (node : RawNode) (child : Nat)
    (valid : NodeTopological size node) (reference : RefersTo node child) : child < size := by
  cases reference with
  | appFn => exact valid.1
  | appArg => exact valid.2
  | lamDomain => exact valid.1
  | lamBody => exact valid.2
  | piDomain => exact valid.1
  | piBody => exact valid.2
  | letType => exact valid.1
  | letValue => exact valid.2.1
  | letBody => exact valid.2.2

theorem topological_edges_decrease (nodes : List RawNode) (parent child : Nat)
    (valid : Topological nodes) (edge : Edge nodes parent child) : child < parent := by
  obtain ⟨node, found, reference⟩ := edge
  have localValid := topologicalFrom_lookup 0 nodes parent node valid found
  rw [Nat.zero_add] at localValid
  exact references_point_backwards parent node child localValid reference

theorem topological_paths_decrease (nodes : List RawNode) (parent child : Nat)
    (valid : Topological nodes) (path : DagPath nodes parent child) : child < parent := by
  induction path with
  | edge edge => exact topological_edges_decrease nodes _ _ valid edge
  | trans first second ihFirst ihSecond => exact Nat.lt_trans ihSecond ihFirst

theorem decoded_dag_has_no_cycles (nodes : List RawNode) (table : List Expr)
    (decoded : decode nodes = some table) (index : Nat) : ¬ DagPath nodes index index := by
  intro cycle
  have valid := (decode_success_iff_topological nodes).1 ⟨table, decoded⟩
  exact Nat.lt_irrefl index (topological_paths_decrease nodes index index valid cycle)

theorem decodeFrom_append (table : List Expr) (left right : List RawNode) :
    decodeFrom table (left ++ right) = (decodeFrom table left).bind (fun prior => decodeFrom prior right) := by
  induction left generalizing table with
  | nil => rfl
  | cons node rest ih =>
    change (match decodeNode table node with
      | none => none
      | some expression => decodeFrom (table ++ [expression]) (rest ++ right)) =
      (match decodeNode table node with
      | none => none
      | some expression => decodeFrom (table ++ [expression]) rest).bind
        (fun prior => decodeFrom prior right)
    cases first : decodeNode table node with
    | none => rfl
    | some expression => exact ih (table ++ [expression])

theorem decode_append (left right : List RawNode) (prior : List Expr)
    (decoded : decode left = some prior) : decode (left ++ right) = decodeFrom prior right := by
  change decodeFrom [] (left ++ right) = decodeFrom prior right
  rw [decodeFrom_append]
  change (decode left).bind _ = _
  rw [decoded]
  rfl

theorem representsFrom_extends {table : List Expr} {nodes : List RawNode} {result : List Expr}
    (represented : RepresentsFrom table nodes result) : ∃ suffix, result = table ++ suffix := by
  induction represented with
  | nil table => exact ⟨[], (append_nil_exact table).symm⟩
  | @cons table node expression rest result first tail ih =>
    obtain ⟨suffix, extensionEq⟩ := ih
    refine ⟨expression :: suffix, ?_⟩
    rw [extensionEq, append_assoc_exact]
    rfl

theorem decode_prefix_extends (left right : List RawNode) (prior result : List Expr)
    (leftDecoded : decode left = some prior) (allDecoded : decode (left ++ right) = some result) :
    ∃ suffix, result = prior ++ suffix := by
  rw [decode_append left right prior leftDecoded] at allDecoded
  exact representsFrom_extends (decodeFrom_sound prior right result allDecoded)

theorem decode_preserves_old_node (left right : List RawNode) (prior result : List Expr)
    (leftDecoded : decode left = some prior) (allDecoded : decode (left ++ right) = some result)
    (index : Nat) (expression : Expr) (old : lookup prior index = some expression) :
    lookup result index = some expression := by
  obtain ⟨suffix, extensionEq⟩ := decode_prefix_extends left right prior result leftDecoded allDecoded
  rw [extensionEq]
  exact at_append_preserves prior suffix index expression old

theorem representsNode_append_preserves {table : List Expr} {node : RawNode} {expression : Expr}
    (represented : RepresentsNode table node expression) (suffix : List Expr) :
    RepresentsNode (table ++ suffix) node expression := by
  cases represented with
  | sort => exact RepresentsNode.sort _
  | var => exact RepresentsNode.var _
  | const => exact RepresentsNode.const _
  | app ha hb => exact RepresentsNode.app (at_append_preserves _ _ _ _ ha) (at_append_preserves _ _ _ _ hb)
  | lam ha hb => exact RepresentsNode.lam (at_append_preserves _ _ _ _ ha) (at_append_preserves _ _ _ _ hb)
  | pi ha hb => exact RepresentsNode.pi (at_append_preserves _ _ _ _ ha) (at_append_preserves _ _ _ _ hb)
  | letE ha hb hc =>
    exact RepresentsNode.letE
      (at_append_preserves _ _ _ _ ha) (at_append_preserves _ _ _ _ hb) (at_append_preserves _ _ _ _ hc)

theorem decodeNode_append_preserves (table suffix : List Expr) (node : RawNode) (expression : Expr)
    (decoded : decodeNode table node = some expression) :
    decodeNode (table ++ suffix) node = some expression :=
  decodeNode_complete (representsNode_append_preserves (decodeNode_sound table node expression decoded) suffix)

theorem shared_application_decodes (table : List Expr) (index : Nat) (expression : Expr)
    (child : lookup table index = some expression) :
    decodeNode table (.app index index) = some (.app expression expression) :=
  decodeNode_complete (RepresentsNode.app child child)

theorem duplicated_children_decode_equally (table : List Expr) (first second : Nat) (expression : Expr)
    (left : lookup table first = some expression) (right : lookup table second = some expression) :
    decodeNode table (.app first second) = decodeNode table (.app first first) :=
  (decodeNode_complete (RepresentsNode.app left right)).trans (shared_application_decodes table first expression left).symm

theorem duplicate_node_decodes_same (table : List Expr) (node : RawNode) (expression : Expr)
    (decoded : decodeNode table node = some expression) :
    decodeFrom table [node, node] = some (table ++ [expression, expression]) := by
  rw [decodeFrom, decoded]
  change decodeFrom (table ++ [expression]) [node] = _
  rw [decodeFrom, decodeNode_append_preserves table [expression] node expression decoded]
  change some ((table ++ [expression]) ++ [expression]) = _
  rw [append_assoc_exact]
  rfl

theorem self_or_forward_reference_rejected (table : List Expr) (node : RawNode) (index : Nat)
    (reference : RefersTo node index) (outside : table.length ≤ index) : decodeNode table node = none := by
  cases decoded : decodeNode table node with
  | none => rfl
  | some expression =>
    have valid := representsNode_topological (decodeNode_sound table node expression decoded)
    exact False.elim (Nat.not_lt_of_ge outside (references_point_backwards _ _ _ valid reference))

/- Natural max/subtraction facts proved without proposition extensionality. -/
theorem max_le_parts (a b bound : Nat) :
    Nat.max a b ≤ bound ↔ a ≤ bound ∧ b ≤ bound := by
  change (if a ≤ b then b else a) ≤ bound ↔ a ≤ bound ∧ b ≤ bound
  by_cases ordered : a ≤ b
  · rw [ite_eq_left ordered]
    exact ⟨fun h => ⟨Nat.le_trans ordered h, h⟩, fun h => h.2⟩
  · rw [ite_eq_right ordered]
    have reverse : b ≤ a := Nat.le_of_lt (Nat.lt_of_not_ge ordered)
    exact ⟨fun h => ⟨h, Nat.le_trans reverse h⟩, fun h => h.1⟩

theorem sub_one_le (value depth : Nat) : value - 1 ≤ depth ↔ value ≤ depth + 1 := by
  cases value with
  | zero => exact ⟨fun _ => Nat.zero_le _, fun _ => Nat.zero_le _⟩
  | succ value =>
    change value ≤ depth ↔ value + 1 ≤ depth + 1
    exact ⟨Nat.succ_le_succ, Nat.le_of_succ_le_succ⟩

theorem scoped_iff_loose (expression : Expr) (depth : Nat) :
    Scoped depth expression ↔ loose expression ≤ depth := by
  induction expression generalizing depth with
  | sort level =>
    exact ⟨fun _ => Nat.zero_le _, fun _ => Scoped.sort _ _⟩
  | var index =>
    constructor
    · intro h; cases h with | var inside => exact inside
    · intro h; exact Scoped.var h
  | const name =>
    exact ⟨fun _ => Nat.zero_le _, fun _ => Scoped.const _ _⟩
  | app a b iha ihb =>
    constructor
    · intro h
      cases h with
      | app ha hb => exact (max_le_parts _ _ _).2 ⟨(iha depth).1 ha, (ihb depth).1 hb⟩
    · intro h
      have parts := (max_le_parts _ _ _).1 h
      exact Scoped.app ((iha depth).2 parts.1) ((ihb depth).2 parts.2)
  | lam a b iha ihb =>
    constructor
    · intro h
      cases h with
      | lam ha hb =>
        exact (max_le_parts _ _ _).2
          ⟨(iha depth).1 ha, (sub_one_le _ _).2 ((ihb (depth + 1)).1 hb)⟩
    · intro h
      have parts := (max_le_parts _ _ _).1 h
      exact Scoped.lam ((iha depth).2 parts.1) ((ihb (depth + 1)).2 ((sub_one_le _ _).1 parts.2))
  | pi a b iha ihb =>
    constructor
    · intro h
      cases h with
      | pi ha hb =>
        exact (max_le_parts _ _ _).2
          ⟨(iha depth).1 ha, (sub_one_le _ _).2 ((ihb (depth + 1)).1 hb)⟩
    · intro h
      have parts := (max_le_parts _ _ _).1 h
      exact Scoped.pi ((iha depth).2 parts.1) ((ihb (depth + 1)).2 ((sub_one_le _ _).1 parts.2))
  | letE a b c iha ihb ihc =>
    constructor
    · intro h
      cases h with
      | letE ha hb hc =>
        exact (max_le_parts _ _ _).2 ⟨(iha depth).1 ha,
          (max_le_parts _ _ _).2 ⟨(ihb depth).1 hb, (sub_one_le _ _).2 ((ihc (depth + 1)).1 hc)⟩⟩
    · intro h
      have first := (max_le_parts _ _ _).1 h
      have rest := (max_le_parts _ _ _).1 first.2
      exact Scoped.letE ((iha depth).2 first.1) ((ihb depth).2 rest.1)
        ((ihc (depth + 1)).2 ((sub_one_le _ _).1 rest.2))

theorem closed_iff_loose_zero (expression : Expr) : Closed expression ↔ loose expression = 0 := by
  constructor
  · intro h
    exact Nat.le_antisymm ((scoped_iff_loose expression 0).1 h) (Nat.zero_le _)
  · intro h
    apply (scoped_iff_loose expression 0).2
    rw [h]
    exact Nat.le_refl _

theorem scoped_monotone (expression : Expr) (small large : Nat)
    (ordered : small ≤ large) (within : Scoped small expression) : Scoped large expression :=
  (scoped_iff_loose expression large).2
    (Nat.le_trans ((scoped_iff_loose expression small).1 within) ordered)

theorem scopeCheck_correct (expression : Expr) (depth : Nat) :
    scopeCheck expression depth = true ↔ Scoped depth expression := by
  unfold scopeCheck
  by_cases enough : loose expression ≤ depth
  · rw [ite_eq_left enough]
    exact ⟨fun _ => (scoped_iff_loose expression depth).2 enough, fun _ => rfl⟩
  · rw [ite_eq_right enough]
    constructor
    · intro impossible; cases impossible
    · intro h; exact False.elim (enough ((scoped_iff_loose expression depth).1 h))

theorem lambda_scope_distinguishes_domain_and_body (domain body : Expr) (depth : Nat) :
    Scoped depth (.lam domain body) ↔ Scoped depth domain ∧ Scoped (depth + 1) body := by
  constructor
  · intro h; cases h with | lam hd hb => exact ⟨hd, hb⟩
  · intro h; exact Scoped.lam h.1 h.2

theorem pi_scope_distinguishes_domain_and_body (domain body : Expr) (depth : Nat) :
    Scoped depth (.pi domain body) ↔ Scoped depth domain ∧ Scoped (depth + 1) body := by
  constructor
  · intro h; cases h with | pi hd hb => exact ⟨hd, hb⟩
  · intro h; exact Scoped.pi h.1 h.2

theorem let_scope_distinguishes_value_and_body (type value body : Expr) (depth : Nat) :
    Scoped depth (.letE type value body) ↔
      Scoped depth type ∧ Scoped depth value ∧ Scoped (depth + 1) body := by
  constructor
  · intro h; cases h with | letE ht hv hb => exact ⟨ht, hv, hb⟩
  · intro h; exact Scoped.letE h.1 h.2.1 h.2.2

theorem variable_requires_exact_depth (index depth : Nat) :
    Scoped depth (.var index) ↔ index < depth := by
  constructor
  · intro h; cases h with | var inside => exact inside
  · intro h; exact Scoped.var h

theorem height_positive (expression : Expr) : 0 < height expression := by
  cases expression <;> exact Nat.zero_lt_succ _

theorem max_left_le (a b : Nat) : a ≤ Nat.max a b :=
  ((max_le_parts a b (Nat.max a b)).1 (Nat.le_refl _)).1

theorem max_right_le (a b : Nat) : b ≤ Nat.max a b :=
  ((max_le_parts a b (Nat.max a b)).1 (Nat.le_refl _)).2

theorem child_height_lt {child parent : Expr} (related : DirectChild child parent) :
    height child < height parent := by
  cases related with
  | appFn => exact Nat.lt_succ_of_le (max_left_le _ _)
  | appArg => exact Nat.lt_succ_of_le (max_right_le _ _)
  | lamDomain => exact Nat.lt_succ_of_le (max_left_le _ _)
  | lamBody => exact Nat.lt_succ_of_le (max_right_le _ _)
  | piDomain => exact Nat.lt_succ_of_le (max_left_le _ _)
  | piBody => exact Nat.lt_succ_of_le (max_right_le _ _)
  | letType => exact Nat.lt_succ_of_le (max_left_le _ _)
  | letValue => exact Nat.lt_succ_of_le (Nat.le_trans (max_left_le _ _) (max_right_le _ _))
  | letBody => exact Nat.lt_succ_of_le (Nat.le_trans (max_right_le _ _) (max_right_le _ _))

theorem refused_observation_is_empty (nodes : List RawNode) (depths : List Nat)
    (refused : decode nodes = none) : observe nodes depths = ⟨false, [], [], [], [], false⟩ := by
  unfold observe
  rw [refused]

theorem observe_has_no_authority (nodes : List RawNode) (depths : List Nat) :
    (observe nodes depths).acceptanceAuthority = false := by
  unfold observe
  cases decode nodes <;> rfl

end GooseExpressionDag

import TypingConversion
import Lean.Data.Json

/-!
Strict JSONL evaluator for the declared typing/conversion fragment. The exact
request keys are nodes, definitions, fuel; names use ASCII byte arrays.
Malformed framing/topology/selectors are process failures, not semantic refusals.
The replay envelope permits 1..128 nodes, 1..64 definitions, and fuel 0..256.
An aggregate 65,536-token expanded raw-wire limit is checked before decoding.
The model itself is unrestricted over finite syntax and natural recursion fuel.
-/
namespace GooseTypingReplay
open GooseExpressionDag GooseTypingConversion Lean

def asciiDigit (c : Char) : Bool := c.toNat ≥ 48 && c.toNat ≤ 57

/-- This schema has precisely three quoted keys and no string-valued fields.
Checking that fact before Json.parse prevents duplicate keys from being lost
by its map representation. Outside strings, only integer and JSON punctuation
characters are permitted, so 1.0, 1e0, booleans, and null cannot become Nats.
Json.getNat? rejects negative integer values; JSON -0 has the same value as 0.
Json.parse remains responsible for full JSON syntax and string escapes. -/
def wireCharacters : List Char → Bool → Bool → Nat → Bool
  | [], inside, escaped, quotes => !inside && !escaped && quotes == 6
  | c :: rest, inside, escaped, quotes =>
    if inside then
      if escaped then wireCharacters rest true false quotes
      else if c == '\\' then wireCharacters rest true true quotes
      else if c == '"' then wireCharacters rest false false (quotes + 1)
      else wireCharacters rest true false quotes
    else if c == '"' then wireCharacters rest true false (quotes + 1)
    else if asciiDigit c || c == '-' || c == '[' || c == ']' || c == '{' || c == '}' ||
        c == ':' || c == ',' || c == ' ' || c == '\t' || c == '\r' || c == '\n' then
      wireCharacters rest false false quotes
    else false

def naturalArray (value : Json) : Except String (List Nat) := do
  (← value.getArr?).toList.mapM Json.getNat?

def nameCode (n : Nat) : Bool :=
  (n ≥ 48 && n ≤ 57) || (n ≥ 65 && n ≤ 90) || (n ≥ 97 && n ≤ 122) || n == 95

def rawNode (value : Json) : Except String RawNode := do
  match (← value.getArr?).toList with
  | [tagJson, aJson, bJson, cJson, namesJson] =>
    let tag ← tagJson.getNat?
    let a ← aJson.getNat?
    let b ← bJson.getNat?
    let c ← cJson.getNat?
    let names ← naturalArray namesJson
    if tag != 2 && !names.isEmpty then throw "only constant nodes may contain name codes"
    match tag with
    | 0 =>
      if b != 0 || c != 0 then throw "sort unused fields must be zero"
      return .sort a
    | 1 =>
      if b != 0 || c != 0 then throw "variable unused fields must be zero"
      return .var a
    | 2 =>
      if a != 0 || b != 0 || c != 0 then throw "constant numeric fields must be zero"
      if names.isEmpty || !names.all nameCode then throw "constant names must be nonempty ASCII alphanumeric/underscore codes"
      return .const names
    | 3 =>
      if c != 0 then throw "application unused field must be zero"
      return .app a b
    | 4 =>
      if c != 0 then throw "lambda unused field must be zero"
      return .lam a b
    | 5 =>
      if c != 0 then throw "Pi unused field must be zero"
      return .pi a b
    | 6 => return .letE a b c
    | _ => throw "unsupported expression node tag"
  | _ => throw "a node must contain exactly tag,a,b,c,nameCodes"

/-- Pre-decode serialization envelope: count expanded prefix-wire tokens for
    every raw node, including unreachable nodes, before recursive semantics. -/
def wireSize (sizes : List Nat) : RawNode → Except String Nat
  | .sort _ | .var _ => .ok 2
  | .const name => .ok (2 + name.length)
  | .app a b | .lam a b | .pi a b => do
    let x ← match lookup sizes a with
      | none => .error "node table must be topological"
      | some size => .ok size
    let y ← match lookup sizes b with
      | none => .error "node table must be topological"
      | some size => .ok size
    return 1 + x + y
  | .letE a b c => do
    let x ← match lookup sizes a with
      | none => .error "node table must be topological"
      | some size => .ok size
    let y ← match lookup sizes b with
      | none => .error "node table must be topological"
      | some size => .ok size
    let z ← match lookup sizes c with
      | none => .error "node table must be topological"
      | some size => .ok size
    return 1 + x + y + z

def checkWireBudget (sizes : List Nat) (used : Nat) : List RawNode → Except String Unit
  | [] => .ok ()
  | node :: rest => do
    let size ← wireSize sizes node
    if used + size > 65536 then throw "expanded raw-node wire inventory exceeds 65536 tokens"
    checkWireBudget (sizes ++ [size]) (used + size) rest

def definition (table : List Expr) (value : Json) : Except String Definition := do
  match (← value.getArr?).toList with
  | [nameJson, typeJson, valueJson] =>
    let name ← naturalArray nameJson
    if name.isEmpty || !name.all nameCode then throw "definition name must be nonempty ASCII alphanumeric/underscore codes"
    let typeIndex ← typeJson.getNat?
    let valueIndex ← valueJson.getNat?
    let type ← match lookup table typeIndex with
      | none => throw "definition type selector is outside the node table"
      | some expression => pure expression
    let expression ← match lookup table valueIndex with
      | none => throw "definition value selector is outside the node table"
      | some expression => pure expression
    return ⟨name, type, expression⟩
  | _ => throw "a definition must contain exactly nameCodes,typeId,valueId"

def replay (line : String) : Except String Observation := do
  if !wireCharacters line.toList false false 0 then
    throw "expected three JSON keys and natural-integer array fields"
  let json ← Json.parse line
  let fields := (← json.getObj?).toList
  if fields.length != 3 || !fields.all (fun entry =>
      entry.1 == "nodes" || entry.1 == "definitions" || entry.1 == "fuel") then
    throw "input object must contain exactly nodes,definitions,fuel"
  let fuel ← (← json.getObjVal? "fuel").getNat?
  if fuel > 256 then throw "model recursion budget exceeds replay bound 256"
  let nodes ← (← (← json.getObjVal? "nodes").getArr?).toList.mapM rawNode
  if nodes.isEmpty || nodes.length > 128 then throw "node inventory must contain 1..128 nodes"
  checkWireBudget [] 0 nodes
  let table ← match decode nodes with
    | none => throw "node table must be topological"
    | some expressions => pure expressions
  let values := (← (← json.getObjVal? "definitions").getArr?).toList
  if values.isEmpty || values.length > 64 then throw "definition inventory must contain 1..64 entries"
  let definitions ← values.mapM (definition table)
  return observe fuel definitions

def boolean (value : Bool) : String := if value then "true" else "false"

def naturalsJson (values : List Nat) : String :=
  "[" ++ String.intercalate "," (values.map toString) ++ "]"

def bindingJson (binding : Binding) : String :=
  "{\"name\":" ++ naturalsJson binding.name ++
  ",\"type\":" ++ naturalsJson (encode binding.ty) ++
  ",\"value\":" ++ naturalsJson (encode binding.value) ++
  ",\"inferred\":" ++ naturalsJson (encode binding.inferred) ++ "}"

def stepJson (step : Step) : String :=
  "{\"name\":" ++ naturalsJson step.name ++ ",\"outcome\":" ++ toString step.outcome ++
  ",\"bindings\":[" ++ String.intercalate "," (step.environment.map bindingJson) ++ "]}"

def observationJson (value : Observation) : String :=
  "{\"schema\":\"lean-goose.typing-conversion-model.v1\",\"steps\":[" ++
  String.intercalate "," (value.steps.map stepJson) ++
  "],\"halted\":" ++ boolean value.halted ++
  ",\"acceptance_authority\":" ++ boolean value.acceptanceAuthority ++ "}"

end GooseTypingReplay

def main : IO UInt32 := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  let errors ← IO.getStderr
  let mut processed := false
  repeat
    let raw ← input.getLine
    if raw.isEmpty then
      if processed then return 0
      errors.putStrLn "invalid typing/conversion replay input: at least one JSON line is required"
      return 2
    let line := if raw.endsWith "\n" then (raw.dropEnd 1).toString else raw
    match GooseTypingReplay.replay line with
    | .error message =>
      errors.putStrLn ("invalid typing/conversion replay input: " ++ message)
      return 2
    | .ok observation =>
      output.putStrLn (GooseTypingReplay.observationJson observation)
      processed := true
  return 0

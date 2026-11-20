import ExpressionDag
import Lean.Data.Json

/-!
JSONL replay for the expression/DAG model. Each input object has exactly
`nodes` and `depths`; a raw node is [tag,a,b,c,nameCodes]. Numeric fields use
nonnegative JSON integer syntax. Unknown/duplicate fields, noncanonical unused
fields, invalid names, and malformed syntax are process errors. A well-formed
wire containing a bad child reference instead produces an atomic decoded=false
model observation. The proof model itself has no finite replay bounds.
-/
namespace GooseExpressionReplay
open GooseExpressionDag Lean

def asciiDigit (c : Char) : Bool := c.toNat ≥ 48 && c.toNat ≤ 57

/-- This schema has precisely two quoted keys and no string-valued fields.
Checking that fact before Json.parse prevents duplicate keys from being lost
by its map representation. Outside strings, only integer and JSON punctuation
characters are permitted, so 1.0, 1e0, booleans, and null cannot become Nats.
Json.getNat? rejects negative integer values; JSON -0 has the same value as 0.
Json.parse remains responsible for full JSON syntax and string escapes. -/
def wireCharacters : List Char → Bool → Bool → Nat → Bool
  | [], inside, escaped, quotes => !inside && !escaped && quotes == 4
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

def replay (line : String) : Except String Projection := do
  if !wireCharacters line.toList false false 0 then
    throw "expected two JSON keys and natural-integer array fields"
  let json ← Json.parse line
  let fields := (← json.getObj?).toList
  if fields.length != 2 || !fields.all (fun entry => entry.1 == "nodes" || entry.1 == "depths") then
    throw "input object must contain exactly nodes and depths"
  let nodesJson ← json.getObjVal? "nodes"
  let depthsJson ← json.getObjVal? "depths"
  let nodes ← (← nodesJson.getArr?).toList.mapM rawNode
  let depths ← naturalArray depthsJson
  return observe nodes depths

def boolean (value : Bool) : String := if value then "true" else "false"

def naturalsJson (values : List Nat) : String :=
  "[" ++ String.intercalate "," (values.map toString) ++ "]"

def booleansJson (values : List Bool) : String :=
  "[" ++ String.intercalate "," (values.map boolean) ++ "]"

def projectionJson (value : Projection) : String :=
  "{\"decoded\":" ++ boolean value.decoded ++
  ",\"expressions\":[" ++ String.intercalate "," (value.expressions.map naturalsJson) ++
  "],\"heights\":" ++ naturalsJson value.heights ++
  ",\"loose\":" ++ naturalsJson value.loose ++
  ",\"scoped\":[" ++ String.intercalate "," (value.scopeResults.map booleansJson) ++
  "],\"acceptance_authority\":" ++ boolean value.acceptanceAuthority ++ "}"

end GooseExpressionReplay

def main : IO UInt32 := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  let errors ← IO.getStderr
  let mut processed := false
  repeat
    let raw ← input.getLine
    if raw.isEmpty then
      if processed then return 0
      errors.putStrLn "invalid expression-DAG replay input: at least one JSON line is required"
      return 2
    let line := if raw.endsWith "\n" then (raw.dropEnd 1).toString else raw
    match GooseExpressionReplay.replay line with
    | .error message =>
      errors.putStrLn ("invalid expression-DAG replay input: " ++ message)
      return 2
    | .ok observation =>
      output.putStrLn (GooseExpressionReplay.projectionJson observation)
      processed := true
  return 0

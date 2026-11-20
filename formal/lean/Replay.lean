import DefinitionTransactions

/-!
Finite replay adapter for the executable transaction model.

Each input line is a nonempty sequence `kind,name,target;kind,name,target`.
Kinds are 0=good, 1=mismatch, 2=alias, 3=scope failure. Numeric fields are strict
ASCII naturals. Each output line is a model-state projection used by the
cross-language checker. A halted projection is diagnostic state, not a completed
definition observation receipt; `GooseTransactions.receipt` returns none there.
-/
namespace GooseReplay
open GooseTransactions

def natural (text : String) : Except String Nat := do
  if text.isEmpty || !text.toList.all Char.isDigit then
    throw "numeric fields must contain nonempty ASCII decimal digits"
  match text.toNat? with
  | some value => return value
  | none => throw "invalid natural number"

def action (text : String) : Except String Action := do
  match text.splitOn "," with
  | [kindText, nameText, targetText] =>
    let code ← natural kindText
    let name ← natural nameText
    let target ← natural targetText
    let kind ← match code with
      | 0 => pure Kind.good
      | 1 => pure Kind.mismatch
      | 2 => pure Kind.alias
      | 3 => pure Kind.scope
      | _ => throw "unsupported transaction action kind"
    return ⟨kind, name, target⟩
  | _ => throw "an action must contain exactly three comma-separated fields"

def actions (line : String) : Except String (List Action) := do
  if line.isEmpty then throw "a transaction trace must be nonempty"
  (line.splitOn ";").mapM action

def boolean (value : Bool) : String := if value then "true" else "false"

def observationJson (value : Observation) : String :=
  "{\"name\":" ++ toString value.name ++ ",\"code\":" ++ toString value.code ++ "}"

def stateJson (state : State) : String :=
  "{\"halted\":" ++ boolean state.halted ++
  ",\"outcomes\":[" ++ String.intercalate "," (state.outcomes.map observationJson) ++
  "],\"environment\":[" ++ String.intercalate "," (state.environment.map toString) ++
  "],\"successes\":" ++ toString state.environment.length ++
  ",\"acceptance_authority\":" ++ boolean state.acceptanceAuthority ++ "}"

end GooseReplay

def main : IO UInt32 := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  let errors ← IO.getStderr
  repeat
    let raw ← input.getLine
    if raw.isEmpty then return 0
    let line := if raw.endsWith "\n" then (raw.dropEnd 1).toString else raw
    match GooseReplay.actions line with
    | .error message =>
      errors.putStrLn ("invalid transaction replay input: " ++ message)
      return 2
    | .ok actions =>
      output.putStrLn (GooseReplay.stateJson (GooseTransactions.run GooseTransactions.initial actions))
  return 0

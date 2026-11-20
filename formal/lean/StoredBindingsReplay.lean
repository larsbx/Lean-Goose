import StoredBindings

/-!
Executable replay for stored binding observations. Each nonempty stdin line is
`kind,name,target,level;...`, using four strict ASCII natural fields per action.
The output includes a snapshot after every processed action. Scope failure has
snapshot code 1 and no semantic outcome; subsequent input actions are ignored.
Halted output is diagnostic model state, not a completed definition receipt.
-/
namespace GooseStoredReplay
open GooseStoredBindings

def natural (text : String) : Except String Nat := do
  if text.isEmpty || !text.toList.all Char.isDigit then
    throw "numeric fields must contain nonempty ASCII decimal digits"
  match text.toNat? with
  | some value => return value
  | none => throw "invalid natural number"

def action (text : String) : Except String Action := do
  match text.splitOn "," with
  | [kindText, nameText, targetText, levelText] =>
    let code ← natural kindText
    let name ← natural nameText
    let target ← natural targetText
    let level ← natural levelText
    let kind ← match code with
      | 0 => pure GooseTransactions.Kind.good
      | 1 => pure GooseTransactions.Kind.mismatch
      | 2 => pure GooseTransactions.Kind.alias
      | 3 => pure GooseTransactions.Kind.scope
      | _ => throw "unsupported stored-binding action kind"
    return ⟨kind, name, target, level⟩
  | _ => throw "an action must contain exactly four comma-separated fields"

def actions (line : String) : Except String (List Action) := do
  if line.isEmpty then throw "a stored-binding trace must be nonempty"
  (line.splitOn ";").mapM action

def boolean (value : Bool) : String := if value then "true" else "false"

def payloadJson (value : List Nat) : String :=
  "[" ++ String.intercalate "," (value.map toString) ++ "]"

def bindingJson (b : Binding) : String :=
  "{\"name\":" ++ toString b.name ++ ",\"type\":" ++ payloadJson b.type ++
  ",\"value\":" ++ payloadJson b.value ++ ",\"inferred\":" ++ payloadJson b.inferred ++ "}"

def environmentJson (environment : List Binding) : String :=
  "[" ++ String.intercalate "," (environment.map bindingJson) ++ "]"

def observationJson (value : GooseTransactions.Observation) : String :=
  "{\"name\":" ++ toString value.name ++ ",\"code\":" ++ toString value.code ++ "}"

def snapshotJson (value : Snapshot) : String :=
  "{\"name\":" ++ toString value.name ++ ",\"code\":" ++ toString value.code ++
  ",\"environment\":" ++ environmentJson value.environment ++ "}"

def stateJson (state : State) : String :=
  "{\"halted\":" ++ boolean state.halted ++
  ",\"environment\":" ++ environmentJson state.environment ++
  ",\"outcomes\":[" ++ String.intercalate "," (state.outcomes.map observationJson) ++
  "],\"successes\":" ++ toString state.environment.length ++
  ",\"acceptance_authority\":" ++ boolean state.acceptanceAuthority ++
  ",\"snapshots\":[" ++ String.intercalate "," (state.snapshots.map snapshotJson) ++ "]}"

end GooseStoredReplay

def main : IO UInt32 := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  let errors ← IO.getStderr
  repeat
    let raw ← input.getLine
    if raw.isEmpty then return 0
    let line := if raw.endsWith "\n" then (raw.dropEnd 1).toString else raw
    match GooseStoredReplay.actions line with
    | .error message =>
      errors.putStrLn ("invalid stored-binding replay input: " ++ message)
      return 2
    | .ok actions =>
      output.putStrLn (GooseStoredReplay.stateJson (GooseStoredBindings.run GooseStoredBindings.initial actions))
  return 0

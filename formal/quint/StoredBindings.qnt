// Scoped stored-binding transactions. Payload vectors are opaque expressions;
// this model does not implement general inference, substitution, or conversion.
module StoredBindings {
  type Input = { kind: int, name: int, target: int, level: int }
  // `type` is a Quint keyword. The replay wire exports this `ty` field as `type`.
  type Binding = { name: int, ty: List[int], value: List[int], inferred: List[int] }
  type Observation = { name: int, code: int }
  type Snapshot = { name: int, code: int, environment: List[Binding] }
  type State = {
    environment: List[Binding], outcomes: List[Observation], halted: bool,
    acceptance_authority: bool, snapshots: List[Snapshot],
  }

  pure def input(kind: int, name: int, target: int, level: int): Input =
    { kind: kind, name: name, target: target, level: level }
  pure val initial: State = {
    environment: List(), outcomes: List(), halted: false,
    acceptance_authority: false, snapshots: List(),
  }
  pure def sort(level: int): List[int] = List(0, level)
  pure def constant(name: int): List[int] = List(2, name)
  // A left-to-right overwrite selects the most recent matching record, even
  // for hypothetical inputs outside the reachable unique-name invariant.
  pure def lookup(environment: List[Binding], name: int): List[Binding] =
    environment.foldl(List(), (found, binding) => if (binding.name == name) List(binding) else found)
  pure def hasName(state: State, name: int): bool = lookup(state.environment, name).length() > 0
  pure def code(state: State, request: Input): int =
    if (hasName(state, request.name)) 3
    else if (request.kind == 0) 0
    else if (request.kind == 1) 6
    else if (request.kind == 2) {
      val found = lookup(state.environment, request.target)
      if (found.length() == 0) 2
      else if (found.nth(0).ty == sort(request.level + 1)) 0
      else 6
    } else 1
  pure def bindingFor(state: State, request: Input): Binding =
    if (request.kind == 0) {
      name: request.name, ty: sort(request.level + 1),
      value: sort(request.level), inferred: sort(request.level + 1),
    } else {
      name: request.name, ty: sort(request.level + 1),
      value: constant(request.target), inferred: lookup(state.environment, request.target).nth(0).ty,
    }
  pure def advance(state: State, request: Input): State =
    if (state.halted) state
    else {
      val result = code(state, request)
      val environment = if (result == 0) state.environment.append(bindingFor(state, request))
                        else state.environment
      {
        ...state, environment: environment, halted: result == 1,
        outcomes: if (result == 1) state.outcomes
                  else state.outcomes.append({ name: request.name, code: result }),
        snapshots: state.snapshots.append({ name: request.name, code: result, environment: environment }),
      }
    }
  pure def replay(requests: List[Input]): State =
    requests.foldl(initial, (state, request) => advance(state, request))
  pure def names(environment: List[Binding]): List[int] =
    environment.foldl(List(), (result, binding) => result.append(binding.name))
  pure def successfulNames(state: State): List[int] =
    state.outcomes.foldl(List(), (result, row) => if (row.code == 0) result.append(row.name) else result)
  pure def prefix(old: List[Binding], current: List[Binding]): bool =
    old.length() <= current.length() and old.indices().forall(i => old.nth(i) == current.nth(i))
  pure def distinctNames(state: State): bool =
    state.environment.indices().forall(i => state.environment.indices().forall(j =>
      i == j or state.environment.nth(i).name != state.environment.nth(j).name))
  pure def snapshotSafety(state: State): bool = all {
    state.snapshots.length() == state.outcomes.length() + (if (state.halted) 1 else 0),
    state.outcomes.indices().forall(i => all {
      state.snapshots.nth(i).name == state.outcomes.nth(i).name,
      state.snapshots.nth(i).code == state.outcomes.nth(i).code,
    }),
    state.snapshots.indices().forall(i => prefix(state.snapshots.nth(i).environment, state.environment)),
    if (state.snapshots.length() == 0) state.environment == List()
    else state.snapshots.nth(state.snapshots.length() - 1).environment == state.environment,
    if (state.halted) state.snapshots.nth(state.snapshots.length() - 1).code == 1 else true,
  }
  pure def stateSafety(state: State): bool = all {
    names(state.environment) == successfulNames(state), distinctNames(state),
    not(state.acceptance_authority), snapshotSafety(state),
    state.outcomes.indices().forall(i => Set(0, 2, 3, 6).contains(state.outcomes.nth(i).code)),
  }

  var s: State
  var previous: State
  var last: Input
  var hasStep: bool
  action init = all {
    s' = initial, previous' = initial, last' = input(0, 0, 0, 0), hasStep' = false,
  }
  action perform(request: Input): bool = all {
    s' = advance(s, request), previous' = s, last' = request, hasStep' = true,
  }
  pure val actionInventory = Set(
    input(0, 0, 0, 0), input(0, 1, 0, 0), input(1, 0, 0, 0), input(1, 1, 0, 0),
    input(2, 0, 0, 0), input(2, 0, 1, 0), input(2, 1, 0, 0), input(2, 1, 1, 0),
    input(3, 0, 0, 0), input(3, 1, 0, 0), input(0, 0, 0, 1), input(0, 1, 0, 1),
    input(2, 0, 1, 1), input(2, 1, 0, 1))
  action step = {
    nondet request = actionInventory.oneOf()
    perform(request)
  }
  val refusalAtomicity = (hasStep and not(previous.halted) and code(previous, last) != 0)
    implies s.environment == previous.environment
  val oldBindingsPreserved = hasStep implies prefix(previous.environment, s.environment)
  val haltedAbsorbing = (hasStep and previous.halted) implies s == previous
  val safety = stateSafety(s) and refusalAtomicity and oldBindingsPreserved and haltedAbsorbing

  // Numeric framing preserves every field and vector element. The Python
  // adapter only decodes lengths; actual predictions are evaluated by Quint.
  pure def expressionWire(expression: List[int]): List[int] = List(expression.length()).concat(expression)
  pure def bindingWire(binding: Binding): List[int] = List(binding.name)
    .concat(expressionWire(binding.ty)).concat(expressionWire(binding.value)).concat(expressionWire(binding.inferred))
  pure def environmentWire(environment: List[Binding]): List[int] = List(environment.length())
    .concat(environment.foldl(List(), (result, binding) => result.concat(bindingWire(binding))))
  pure def wire(state: State): List[int] =
    List(if (state.halted) 1 else 0, if (state.acceptance_authority) 1 else 0)
      .concat(environmentWire(state.environment)).concat(List(state.outcomes.length()))
      .concat(state.outcomes.foldl(List(), (result, row) => result.concat(List(row.name, row.code))))
      .concat(List(state.snapshots.length())).concat(state.snapshots.foldl(List(),
        (result, snapshot) => result.concat(List(snapshot.name, snapshot.code)).concat(environmentWire(snapshot.environment))))
  pure def traceWire(requests: List[Input]): List[int] =
    List(requests.length()).concat(requests.foldl(List(), (result, request) =>
      result.concat(List(request.kind, request.name, request.target, request.level))))
      .concat(wire(replay(requests)))
  pure val replayProfile: List[List[int]] = actionInventory.allListsUpTo(3)
    .filter(requests => requests.length() > 0)
    .fold(List(), (result, requests) => result.append(traceWire(requests)))

  run initialStoredStateTest = init.expect(safety and s.environment == List() and s.snapshots == List())
  run goodPayloadLevelZeroTest = init.then(perform(input(0, 0, 0, 0)))
    .expect(safety and s.environment == List({ name: 0, ty: List(0, 1), value: List(0, 0), inferred: List(0, 1) }))
  run goodPayloadLevelOneTest = init.then(perform(input(0, 0, 0, 1)))
    .expect(safety and s.environment == List({ name: 0, ty: List(0, 2), value: List(0, 1), inferred: List(0, 2) }))
  run typedAliasPayloadTest = init.then(perform(input(0, 0, 0, 0))).then(perform(input(2, 1, 0, 0)))
    .expect(safety and s.environment.nth(1) == { name: 1, ty: List(0, 1), value: List(2, 0), inferred: List(0, 1) })
  run wrongTypeAliasRefusalTest = init.then(perform(input(0, 0, 0, 1))).then(perform(input(2, 1, 0, 0)))
    .expect(safety and s.environment == previous.environment and s.outcomes.nth(1).code == 6)
  run duplicatePreservesAllFieldsTest = init.then(perform(input(0, 0, 0, 0))).then(perform(input(0, 0, 0, 1)))
    .expect(safety and s.environment == previous.environment and s.outcomes.nth(1).code == 3)
  run crossLevelDuplicateAliasTest = init.then(perform(input(0, 0, 0, 0))).then(perform(input(2, 0, 1, 1)))
    .expect(safety and s.environment == previous.environment and s.outcomes.nth(1).code == 3)
  run mismatchPreservesAllFieldsTest = init.then(perform(input(0, 0, 0, 1))).then(perform(input(1, 1, 0, 0)))
    .expect(safety and s.environment == previous.environment and s.outcomes.nth(1).code == 6)
  run unknownAliasPreservesAllFieldsTest = init.then(perform(input(0, 0, 0, 1))).then(perform(input(2, 1, 1, 0)))
    .expect(safety and s.environment == previous.environment and s.outcomes.nth(1).code == 2)
  run refusalThenRetryTest = init.then(perform(input(0, 0, 0, 1))).then(perform(input(2, 1, 0, 0)))
    .then(perform(input(2, 1, 0, 1)))
    .expect(safety and s.environment.length() == 2 and s.outcomes.nth(1).code == 6 and s.outcomes.nth(2).code == 0)
  run levelOneAliasTest = init.then(perform(input(0, 1, 0, 1))).then(perform(input(2, 0, 1, 1)))
    .expect(safety and s.environment.nth(1) == { name: 0, ty: List(0, 2), value: List(2, 1), inferred: List(0, 2) })
  run scopeSnapshotTest = init.then(perform(input(0, 0, 0, 0))).then(perform(input(3, 1, 0, 0)))
    .expect(safety and s.halted and s.outcomes.length() == 1 and s.snapshots.length() == 2 and
      s.snapshots.nth(1).code == 1 and s.environment == previous.environment)
  run duplicatePreemptsScopeSnapshotTest = init.then(perform(input(0, 0, 0, 1))).then(perform(input(3, 0, 0, 0)))
    .expect(safety and not(s.halted) and s.snapshots.nth(1).code == 3 and s.environment == previous.environment)
  run haltStopsSnapshotsTest = init.then(perform(input(3, 0, 0, 0))).then(perform(input(0, 1, 0, 0)))
    .expect(safety and s == previous and s.snapshots.length() == 1 and s.outcomes == List())
  run orderedSnapshotCountTest = init.then(perform(input(1, 1, 0, 0)))
    .then(perform(input(0, 0, 0, 0))).then(perform(input(2, 1, 0, 0)))
    .expect(safety and s.snapshots.length() == 3 and s.snapshots.nth(0).environment == List() and
      s.snapshots.nth(1).environment.length() == 1 and s.snapshots.nth(2).environment.length() == 2)
  run storedAuthorityPreservedTest = init.then(perform(input(0, 0, 0, 1))).then(perform(input(2, 1, 0, 1)))
    .expect(safety and not(s.acceptance_authority))

  // Begin at a genuinely reachable populated state. The negative transition
  // refuses a fresh definition but illegally changes an existing value field.
  pure val unsafeStart = advance(initial, input(0, 0, 0, 0))
  action unsafeInit = all {
    s' = unsafeStart, previous' = unsafeStart, last' = input(0, 0, 0, 0), hasStep' = false,
  }
  action unsafeStep = {
    val request = input(1, 1, 0, 0)
    val refused = advance(s, request)
    val corrupted = refused.environment.replaceAt(0, { ...refused.environment.nth(0), value: List(0, 999) })
    val lastIndex = refused.snapshots.length() - 1
    all {
      previous' = s, last' = request, hasStep' = true,
      s' = { ...refused, environment: corrupted, snapshots: refused.snapshots.replaceAt(lastIndex,
        { ...refused.snapshots.nth(lastIndex), environment: corrupted }) },
    }
  }
}

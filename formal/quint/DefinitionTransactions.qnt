// Ordered definition transactions for the declared finite action vocabulary.
// Term inference is represented by action classes; it is not implemented here.
module DefinitionTransactions {
  type Input = { kind: int, name: int, target: int }
  type Observation = { name: int, code: int }
  type State = {
    environment: List[int], outcomes: List[Observation], halted: bool,
    acceptance_authority: bool,
  }

  pure def input(kind: int, name: int, target: int): Input =
    { kind: kind, name: name, target: target }
  pure val initial: State = {
    environment: List(), outcomes: List(), halted: false, acceptance_authority: false,
  }
  pure def hasName(state: State, name: int): bool =
    state.environment.indices().exists(i => state.environment.nth(i) == name)
  pure def emit(state: State, request: Input, code: int): State =
    { ...state, outcomes: state.outcomes.append({ name: request.name, code: code }) }
  pure def insert(state: State, request: Input): State = {
    ...emit(state, request, 0), environment: state.environment.append(request.name),
  }
  pure def advance(state: State, request: Input): State =
    if (state.halted) state
    else if (hasName(state, request.name)) emit(state, request, 3)
    else if (request.kind == 0) insert(state, request)
    else if (request.kind == 1) emit(state, request, 6)
    else if (request.kind == 2)
      if (hasName(state, request.target)) insert(state, request)
      else emit(state, request, 2)
    else { ...state, halted: true }

  pure def replay(requests: List[Input]): State =
    requests.foldl(initial, (state, request) => advance(state, request))
  // A numeric wire vector keeps CLI replay serialization independent of any
  // Python implementation of transaction semantics.
  pure def wire(state: State): List[int] =
    List(if (state.halted) 1 else 0, if (state.acceptance_authority) 1 else 0,
      state.environment.length()).concat(state.environment)
      .concat(List(state.outcomes.length()))
      .concat(state.outcomes.foldl(List(), (values, row) => values.concat(List(row.name, row.code))))
  pure def successfulNames(state: State): List[int] =
    state.outcomes.foldl(List(), (names, row) => if (row.code == 0) names.append(row.name) else names)
  pure def distinctNames(state: State): bool =
    state.environment.indices().forall(i => state.environment.indices().forall(j =>
      i == j or state.environment.nth(i) != state.environment.nth(j)))
  pure def completed(state: State): bool = not(state.halted)
  pure def stateSafety(state: State): bool = all {
    state.environment == successfulNames(state), distinctNames(state),
    not(state.acceptance_authority),
    state.outcomes.indices().forall(i => Set(0, 2, 3, 6).contains(state.outcomes.nth(i).code)),
  }
  // State history lets the simulation check atomicity, including a refusal
  // after successful definitions have already populated the environment.
  pure def refusal(request: Input, before: State): bool = not(before.halted) and (
    hasName(before, request.name) or request.kind == 1 or
    (request.kind == 2 and not(hasName(before, request.target))))

  var s: State
  var previous: State
  var last: Input
  var hasStep: bool

  action init = all {
    s' = initial, previous' = initial, last' = input(0, 0, 0), hasStep' = false,
  }
  action perform(request: Input): bool = all {
    s' = advance(s, request), previous' = s, last' = request, hasStep' = true,
  }
  pure val actionInventory = Set(
    input(0, 0, 0), input(0, 1, 0), input(1, 0, 0), input(1, 1, 0),
    input(2, 0, 0), input(2, 0, 1), input(2, 1, 0), input(2, 1, 1),
    input(3, 0, 0), input(3, 1, 0))
  // Exhaust the declared bounded profile for cross-model comparison. Each
  // result carries its input identity, because set iteration order is arbitrary.
  pure def traceWire(requests: List[Input]): List[int] =
    List(requests.length()).concat(requests.foldl(List(),
      (values, request) => values.concat(List(request.kind, request.name, request.target))))
      .concat(wire(replay(requests)))
  pure val replayProfile: List[List[int]] = actionInventory.allListsUpTo(3)
    .filter(requests => requests.length() > 0)
    .fold(List(), (results, requests) => results.append(traceWire(requests)))

  action step = {
    nondet request = actionInventory.oneOf()
    perform(request)
  }
  val refusalAtomicity = (hasStep and refusal(last, previous)) implies
    s.environment == previous.environment
  val haltedAbsorbing = (hasStep and previous.halted) implies s == previous
  val safety = stateSafety(s) and refusalAtomicity and haltedAbsorbing

  run initialStateTest = init.expect(safety and completed(s) and s.environment == List())
  run successfulDefinitionTest = init.then(perform(input(0, 0, 0)))
    .expect(safety and s.environment == List(0) and s.outcomes == List({ name: 0, code: 0 }))
  run failedInsertionRetryTest = init.then(perform(input(1, 0, 0)))
    .expect(safety and s.environment == List())
    .then(perform(input(0, 0, 0)))
    .expect(safety and s.environment == List(0) and s.outcomes ==
      List({ name: 0, code: 6 }, { name: 0, code: 0 }))
  run duplicatePreservesEnvironmentTest = init.then(perform(input(0, 0, 0)))
    .then(perform(input(0, 0, 0)))
    .expect(safety and s.environment == List(0) and s.outcomes.nth(1).code == 3)
  run duplicatePreemptsScopeTest = init.then(perform(input(0, 0, 0)))
    .then(perform(input(3, 0, 0)))
    .expect(safety and completed(s) and s.environment == List(0) and s.outcomes.nth(1).code == 3)
  run unknownAliasRecoveryTest = init.then(perform(input(2, 0, 1)))
    .expect(safety and s.environment == List() and s.outcomes.nth(0).code == 2)
    .then(perform(input(0, 1, 0))).then(perform(input(2, 0, 1)))
    .expect(safety and s.environment == List(1, 0) and s.outcomes.nth(2).code == 0)
  run validAliasTest = init.then(perform(input(0, 0, 0)))
    .then(perform(input(2, 1, 0)))
    .expect(safety and s.environment == List(0, 1) and s.outcomes.nth(1).code == 0)
  run unknownAliasPreservesExistingTest = init.then(perform(input(0, 0, 0)))
    .then(perform(input(2, 1, 1)))
    .expect(safety and s.environment == List(0) and s.outcomes.nth(1).code == 2)
  run scopeFailureSuppressesReceiptTest = init.then(perform(input(3, 0, 0)))
    .expect(safety and s.halted and not(completed(s)) and s.outcomes == List())
  run haltAbsorbingTest = init.then(perform(input(3, 0, 0)))
    .then(perform(input(0, 1, 0)))
    .expect(safety and s == previous and s.environment == List() and s.outcomes == List())
  run orderedSuccessCountTest = init.then(perform(input(1, 1, 0)))
    .then(perform(input(0, 0, 0))).then(perform(input(2, 1, 0)))
    .expect(safety and s.environment == List(0, 1) and s.environment.length() == 2 and
      s.outcomes == List({ name: 1, code: 6 }, { name: 0, code: 0 }, { name: 1, code: 0 }))
  run authorityPreservedTest = init.then(perform(input(0, 0, 0)))
    .then(perform(input(2, 1, 0)))
    .expect(safety and completed(s) and not(s.acceptance_authority))

  // Designated negative control: a mismatched definition is wrongly inserted.
  // The actual run must find an invariant violation and preserve its ITF trace.
  action unsafeStep = all {
    previous' = s, last' = input(1, 0, 0), hasStep' = true,
    s' = { ...emit(s, input(1, 0, 0), 6), environment: s.environment.append(0) },
  }
}

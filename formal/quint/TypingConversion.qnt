// Numeric-sort, transparent monomorphic typing and beta/zeta/delta conversion.
// The evaluator uses an explicit continuation stack: no Python semantic oracle.
// `fuel` bounds recursive evaluator nesting, independently of native work fuel.
// A separate 2048-transition host-model cap fails closed with code 10; the
// replay adapter rejects that code rather than calling it a checker refusal.
module TypingConversion {
  import Substitution as S from "./Substitution"
  import ExpressionDag as D from "./ExpressionDag"

  type Expr = List[int]
  type Binding = { name: List[int], ty: Expr, value: Expr, inferred: Expr }
  type Definition = { name: List[int], ty: int, value: int }
  type Snapshot = { name: List[int], code: int, bindings: List[Binding] }
  type State = { environment: List[Binding], snapshots: List[Snapshot], halted: bool, acceptance_authority: bool }
  type Task = { op: int, expression: Expr, other: Expr, extra: Expr, context: List[Expr], fuel: int }
  type Machine = { tasks: List[Task], value: Expr, code: int, transitions: int }
  type Result = { value: Expr, code: int }

  pure def sort(level: int): Expr = List(0, level)
  pure def variable(index: int): Expr = List(1, index)
  pure def constant(name: List[int]): Expr = List(2, name.length()).concat(name)
  pure def pair(tag: int, first: Expr, second: Expr): Expr = List(tag).concat(first).concat(second)
  pure def letExpr(ty: Expr, value: Expr, body: Expr): Expr = List(6).concat(ty).concat(value).concat(body)
  pure def definition(name: List[int], ty: int, value: int): Definition = { name: name, ty: ty, value: value }
  pure def arity(tag: int): int = if (tag < 3) 0 else if (tag == 6) 3 else 2
  pure def headerWidth(e: Expr, i: int): int =
    if (e.nth(i) == 2) 2 + e.nth(i + 1) else if (e.nth(i) < 2) 2 else 1

  // Walk only token headers, never interpreting sort/index/name payloads as tags.
  pure def headers(e: Expr): List[int] =
    range(0, e.length()).foldl({ cursor: 0, positions: List() }, (state, i) =>
      if (i != state.cursor) state
      else { cursor: i + headerWidth(e, i), positions: state.positions.append(i) }).positions
  pure def endAt(e: Expr, start: int): int =
    range(start, e.length()).foldl({ cursor: start, pending: 1 }, (state, i) =>
      if (state.pending == 0 or i != state.cursor) state
      else { cursor: i + headerWidth(e, i), pending: state.pending - 1 + arity(e.nth(i)) }).cursor
  pure def first(e: Expr): Expr = e.slice(1, endAt(e, 1))
  pure def second(e: Expr): Expr = {
    val start = endAt(e, 1)
    e.slice(start, endAt(e, start))
  }
  pure def third(e: Expr): Expr = {
    val start = endAt(e, endAt(e, 1))
    e.slice(start, endAt(e, start))
  }

  // Re-encode a structural wire as a backward-reference DAG. This permits
  // direct reuse of the earlier independent Quint lift/substitute definitions.
  pure def arena(e: Expr): List[S::Node] = {
    val positions = headers(e)
    range(0, positions.length()).foldl({ nodes: List(), roots: List() }, (state, reverseIndex) => {
      val i = positions.nth(positions.length() - 1 - reverseIndex)
      val tag = e.nth(i)
      val raw = if (tag < 2) S::leaf(tag, e.nth(i + 1))
        else if (tag == 2) S::node(2, 0, 0, 0, e.slice(i + 2, i + headerWidth(e, i)))
        else if (tag == 6) S::node(tag, state.roots.nth(0), state.roots.nth(1), state.roots.nth(2), List())
        else S::binary(tag, state.roots.nth(0), state.roots.nth(1))
      { nodes: state.nodes.append(raw),
        roots: List(state.nodes.length()).concat(state.roots.slice(arity(tag), state.roots.length())) }
    }).nodes
  }
  pure def shifted(e: Expr, amount: int): Expr = {
    val nodes = arena(e)
    S::liftRoot(nodes, nodes.length() - 1, amount, 0).expression
  }
  pure def replaced(body: Expr, value: Expr): Expr = {
    val nodes = arena(pair(3, body, value))
    val root = nodes.nth(nodes.length() - 1)
    S::substituteRoot(nodes, root.a, root.b, 0).expression
  }
  pure def closed(e: Expr): bool = {
    val nodes = arena(e)
    S::liftRoot(nodes, nodes.length() - 1, 0, 0).loose == 0
  }
  pure def lookup(environment: List[Binding], name: List[int]): List[Binding] =
    environment.foldl(List(), (found, binding) => if (binding.name == name) List(binding) else found)
  pure def known(environment: List[Binding], e: Expr): bool =
    headers(e).indices().forall(j => {
      val i = headers(e).nth(j)
      e.nth(i) != 2 or lookup(environment, e.slice(i + 2, i + headerWidth(e, i))).length() > 0
    })

  // Ops 0..4 are head, normal, infer, sortLevel, convert. Larger op numbers
  // are continuation frames. Each *call* consumes one recursive-depth unit;
  // continuation frames do not. Sibling calls receive the same predecessor.
  pure def task(op: int, e: Expr, other: Expr, extra: Expr, context: List[Expr], fuel: int): Task =
    { op: op, expression: e, other: other, extra: extra, context: context, fuel: fuel }
  pure def call(op: int, e: Expr, context: List[Expr], fuel: int): Task =
    task(op, e, List(), List(), context, fuel)
  pure def push(machine: Machine, tasks: List[Task]): Machine =
    { ...machine, tasks: tasks.concat(machine.tasks) }
  pure def returned(machine: Machine, value: Expr): Machine = { ...machine, value: value }
  pure def failed(machine: Machine, code: int): Machine = { ...machine, code: code, tasks: List() }
  pure def done(machine: Machine): bool = machine.code != 0 or machine.tasks.length() == 0

  pure def tick(environment: List[Binding], input: Machine): Machine =
    if (done(input)) input else {
      val t = input.tasks.nth(0)
      val m = { ...input, tasks: input.tasks.tail(), transitions: input.transitions + 1 }
      val e = t.expression
      val n = t.fuel - 1
      if (t.op <= 4 and t.fuel == 0) failed(m, 9)
      else if (t.op == 0) {
        val tag = e.nth(0)
        if (tag == 2) {
          val found = lookup(environment, e.slice(2, e.length()))
          if (found.length() == 0) failed(m, 2)
          else push(m, List(call(0, found.nth(0).value, t.context, n)))
        } else if (tag == 6) push(m, List(call(0, replaced(third(e), second(e)), t.context, n)))
        else if (tag == 3) push(m, List(call(0, first(e), t.context, n),
          task(10, second(e), List(), List(), t.context, n)))
        else returned(m, e)
      } else if (t.op == 10) {
        if (m.value.nth(0) == 4) push(m, List(call(0, replaced(second(m.value), e), t.context, t.fuel)))
        else returned(m, pair(3, m.value, e))
      } else if (t.op == 1) push(m, List(call(0, e, t.context, n),
        task(11, List(), List(), List(), t.context, n)))
      else if (t.op == 11) {
        val reduced = m.value
        if (Set(3, 4, 5).contains(reduced.nth(0)))
          push(m, List(call(1, first(reduced), t.context, t.fuel),
            task(12, second(reduced), List(reduced.nth(0)), List(), t.context, t.fuel)))
        else returned(m, reduced)
      } else if (t.op == 12) push(m, List(call(1, e, t.context, t.fuel),
        task(13, m.value, t.other, List(), t.context, t.fuel)))
      else if (t.op == 13) returned(m, pair(t.other.nth(0), e, m.value))
      else if (t.op == 2) {
        val tag = e.nth(0)
        if (tag == 0) returned(m, sort(e.nth(1) + 1))
        else if (tag == 1) {
          val index = e.nth(1)
          if (index >= t.context.length()) failed(m, 1)
          else returned(m, shifted(t.context.nth(index), index + 1))
        } else if (tag == 2) {
          val found = lookup(environment, e.slice(2, e.length()))
          if (found.length() == 0) failed(m, 2) else returned(m, found.nth(0).ty)
        } else if (tag == 4) push(m, List(call(3, first(e), t.context, n),
          task(20, first(e), second(e), List(), t.context, n)))
        else if (tag == 5) push(m, List(call(3, first(e), t.context, n),
          task(22, first(e), second(e), List(), t.context, n)))
        else if (tag == 3) push(m, List(call(2, first(e), t.context, n),
          task(24, second(e), List(), List(), t.context, n)))
        else push(m, List(call(3, first(e), t.context, n),
          task(28, first(e), second(e), third(e), t.context, n)))
      } else if (t.op == 20) push(m, List(call(2, t.other, List(e).concat(t.context), t.fuel),
        task(21, e, List(), List(), t.context, t.fuel)))
      else if (t.op == 21) returned(m, pair(5, e, m.value))
      else if (t.op == 22) push(m, List(call(3, t.other, List(e).concat(t.context), t.fuel),
        task(23, m.value, List(), List(), t.context, t.fuel)))
      else if (t.op == 23) returned(m, sort(if (m.value.nth(1) == 0) 0
        else if (e.nth(1) > m.value.nth(1)) e.nth(1) else m.value.nth(1)))
      else if (t.op == 24) push(m, List(call(0, m.value, t.context, t.fuel),
        task(25, e, List(), List(), t.context, t.fuel)))
      else if (t.op == 25) {
        if (m.value.nth(0) != 5) failed(m, 5)
        else push(m, List(call(2, e, t.context, t.fuel),
          task(26, e, first(m.value), second(m.value), t.context, t.fuel)))
      } else if (t.op == 26) push(m, List(task(4, m.value, t.other, List(), t.context, t.fuel),
        task(27, e, t.extra, List(), t.context, t.fuel)))
      else if (t.op == 27) {
        if (m.value.nth(1) == 0) failed(m, 6) else returned(m, replaced(t.other, e))
      } else if (t.op == 28) push(m, List(call(2, t.other, t.context, t.fuel),
        task(29, e, t.other, t.extra, t.context, t.fuel)))
      else if (t.op == 29) push(m, List(task(4, m.value, e, List(), t.context, t.fuel),
        task(30, t.other, t.extra, List(), t.context, t.fuel)))
      else if (t.op == 30) {
        if (m.value.nth(1) == 0) failed(m, 6)
        else push(m, List(call(2, replaced(t.other, e), t.context, t.fuel)))
      } else if (t.op == 3) push(m, List(call(2, e, t.context, n),
        task(31, List(), List(), List(), t.context, n)))
      else if (t.op == 31) push(m, List(call(0, m.value, t.context, t.fuel),
        task(32, List(), List(), List(), t.context, t.fuel)))
      else if (t.op == 32) {
        if (m.value.nth(0) != 0) failed(m, 4) else returned(m, m.value)
      } else if (t.op == 4) push(m, List(call(1, e, t.context, n),
        task(33, t.other, List(), List(), t.context, n)))
      else if (t.op == 33) push(m, List(call(1, e, t.context, t.fuel),
        task(34, m.value, List(), List(), t.context, t.fuel)))
      else if (t.op == 34) returned(m, sort(if (e == m.value) 1 else 0))
      else failed(m, 10)
    }

  // Explicit finite unrolling, with early completion at every level. The bound
  // is reproducible without spending all remaining transitions after success.
  pure def drive2(env: List[Binding], m: Machine): Machine = if (done(m)) m else tick(env, tick(env, m))
  pure def drive4(env: List[Binding], m: Machine): Machine = if (done(m)) m else drive2(env, drive2(env, m))
  pure def drive8(env: List[Binding], m: Machine): Machine = if (done(m)) m else drive4(env, drive4(env, m))
  pure def drive16(env: List[Binding], m: Machine): Machine = if (done(m)) m else drive8(env, drive8(env, m))
  pure def drive32(env: List[Binding], m: Machine): Machine = if (done(m)) m else drive16(env, drive16(env, m))
  pure def drive64(env: List[Binding], m: Machine): Machine = if (done(m)) m else drive32(env, drive32(env, m))
  pure def drive128(env: List[Binding], m: Machine): Machine = if (done(m)) m else drive64(env, drive64(env, m))
  pure def drive256(env: List[Binding], m: Machine): Machine = if (done(m)) m else drive128(env, drive128(env, m))
  pure def drive512(env: List[Binding], m: Machine): Machine = if (done(m)) m else drive256(env, drive256(env, m))
  pure def drive1024(env: List[Binding], m: Machine): Machine = if (done(m)) m else drive512(env, drive512(env, m))
  pure def drive2048(env: List[Binding], m: Machine): Machine = if (done(m)) m else drive1024(env, drive1024(env, m))
  pure def eval(env: List[Binding], op: int, e: Expr, other: Expr, context: List[Expr], fuel: int): Result = {
    val result = drive2048(env, { tasks: List(task(op, e, other, List(), context, fuel)),
      value: List(), code: 0, transitions: 0 })
    if (not(done(result))) { value: List(), code: 10 }
    else { value: result.value, code: result.code }
  }

  pure val initial: State = { environment: List(), snapshots: List(), halted: false, acceptance_authority: false }
  pure def semanticResult(env: List[Binding], ty: Expr, value: Expr, fuel: int): Result = {
    val sorted = eval(env, 3, ty, List(), List(), fuel)
    if (sorted.code != 0) sorted else {
      val inferred = eval(env, 2, value, List(), List(), fuel)
      if (inferred.code != 0) inferred else {
        val normalized = eval(env, 1, inferred.value, List(), List(), fuel)
        if (normalized.code != 0) normalized else {
          val converted = eval(env, 4, normalized.value, ty, List(), fuel)
          if (converted.code != 0) converted
          else if (converted.value.nth(1) == 0) { value: List(), code: 6 }
          else normalized
        }
      }
    }
  }
  pure def check(env: List[Binding], name: List[int], ty: Expr, value: Expr, fuel: int): Result =
    if (lookup(env, name).length() > 0) { value: List(), code: 3 }
    else if (not(closed(ty)) or not(closed(value))) { value: List(), code: 1 }
    else if (not(known(env, ty)) or not(known(env, value))) { value: List(), code: 2 }
    else semanticResult(env, ty, value, fuel)
  pure def advance(state: State, name: List[int], ty: Expr, value: Expr, fuel: int): State =
    if (state.halted) state else {
      val result = check(state.environment, name, ty, value, fuel)
      val bindings = if (result.code == 0)
        state.environment.append({ name: name, ty: ty, value: value, inferred: result.value })
        else state.environment
      { environment: bindings,
        snapshots: state.snapshots.append({ name: name, code: result.code, bindings: bindings }),
        halted: Set(1, 9, 10).contains(result.code), acceptance_authority: false }
    }
  pure def observe(nodes: List[D::Node], definitions: List[Definition], fuel: int): State = {
    val decoded = D::replay(nodes)
    definitions.foldl(initial, (state, d) =>
      advance(state, d.name, decoded.rows.nth(d.ty).expression, decoded.rows.nth(d.value).expression, fuel))
  }

  pure def vectorWire(values: List[int]): List[int] = List(values.length()).concat(values)
  pure def bindingWire(binding: Binding): List[int] = vectorWire(binding.name)
    .concat(vectorWire(binding.ty)).concat(vectorWire(binding.value)).concat(vectorWire(binding.inferred))
  pure def resultWire(state: State): List[int] =
    List(if (state.halted) 1 else 0, if (state.acceptance_authority) 1 else 0, state.snapshots.length())
      .concat(state.snapshots.foldl(List(), (wire, row) => wire.concat(vectorWire(row.name))
        .concat(List(row.code, row.bindings.length())).concat(row.bindings.foldl(List(),
          (bindings, binding) => bindings.concat(bindingWire(binding))))))
  pure def identityWire(id: int, nodes: List[D::Node], definitions: List[Definition], fuel: int): List[int] =
    List(id, nodes.length()).concat(nodes.foldl(List(), (wire, raw) =>
      wire.concat(List(raw.tag, raw.a, raw.b, raw.c)).concat(vectorWire(raw.name))))
      .concat(List(definitions.length())).concat(definitions.foldl(List(), (wire, d) =>
        wire.concat(vectorWire(d.name)).concat(List(d.ty, d.value)))).concat(List(fuel))
  pure def replayRequest(id: int, nodes: List[D::Node], definitions: List[Definition], fuel: int): List[int] =
    identityWire(id, nodes, definitions, fuel).concat(resultWire(observe(nodes, definitions, fuel)))


  type Input = { name: List[int], ty: Expr, value: Expr, fuel: int }
  pure def input(name: List[int], ty: Expr, value: Expr, fuel: int): Input =
    { name: name, ty: ty, value: value, fuel: fuel }
  pure val name0 = List(110, 48)
  pure val name1 = List(110, 49)
  pure val identity = pair(4, sort(1), variable(0))
  pure val identityType = pair(5, sort(1), sort(1))
  pure val defaultInput = input(name0, sort(1), sort(0), 128)
  var s: State
  var previous: State
  var last: Input
  var hasStep: bool
  action init = all { s' = initial, previous' = initial, last' = defaultInput, hasStep' = false }
  action perform(query: Input): bool = all {
    previous' = s, last' = query, hasStep' = true,
    s' = advance(s, query.name, query.ty, query.value, query.fuel),
  }
  pure def prefix(old: List[Binding], current: List[Binding]): bool =
    old.length() <= current.length() and old.indices().forall(i => old.nth(i) == current.nth(i))
  pure def successfulCount(state: State): int =
    state.snapshots.foldl(0, (count, row) => count + (if (row.code == 0) 1 else 0))
  pure def stateSafety(state: State): bool = all {
    not(state.acceptance_authority), state.environment.length() == successfulCount(state),
    state.environment.indices().forall(i => state.environment.indices().forall(j =>
      i == j or state.environment.nth(i).name != state.environment.nth(j).name)),
    state.snapshots.indices().forall(i => prefix(state.snapshots.nth(i).bindings, state.environment)),
    if (state.snapshots.length() == 0) state.environment == List()
    else state.environment == state.snapshots.nth(state.snapshots.length() - 1).bindings,
    state.snapshots.indices().forall(i => Set(0, 1, 2, 3, 4, 5, 6, 9).contains(state.snapshots.nth(i).code)),
  }
  val transitionSafety = if (not(hasStep)) true
    else if (previous.halted) s == previous
    else {
      val checked = check(previous.environment, last.name, last.ty, last.value, last.fuel)
      val newEnvironment = if (checked.code == 0)
        previous.environment.append({ name: last.name, ty: last.ty, value: last.value, inferred: checked.value })
        else previous.environment
      all {
        s.environment == newEnvironment,
        s.snapshots == previous.snapshots.append({ name: last.name, code: checked.code, bindings: newEnvironment }),
        s.halted == Set(1, 9).contains(checked.code),
      }
    }
  val safety = stateSafety(s) and transitionSafety
  action stutter = all { s' = s, previous' = previous, last' = last, hasStep' = hasStep }
  action step = if (s.snapshots.length() >= 4) stutter else {
    nondet name = Set(name0, name1).oneOf()
    nondet kind = 0.to(7).oneOf()
    val query = if (kind == 0) input(name, sort(1), sort(0), 128)
      else if (kind == 1) input(name, identityType, identity, 128)
      else if (kind == 2) input(name, sort(1), pair(3, identity, sort(0)), 128)
      else if (kind == 3) input(name, sort(2), sort(0), 128)
      else if (kind == 4) input(name, sort(1), pair(3, sort(0), sort(0)), 128)
      else if (kind == 5) input(name, sort(1), constant(List(122)), 128)
      else if (kind == 6) input(name, sort(1), variable(0), 128)
      else input(name, sort(1), letExpr(sort(1), sort(0), variable(0)), 128)
    perform(query)
  }

  run initialTypingStateTest = init.expect(safety and s.environment == List())
  run sortInferenceTest = init.then(perform(defaultInput))
    .expect(safety and s.environment.nth(0).inferred == sort(1))
  run lambdaInferenceTest = init.then(perform(input(name0, identityType, identity, 128)))
    .expect(safety and s.environment.nth(0).value == identity and s.environment.nth(0).inferred == identityType)
  run betaValueRetainedTest = init.then(perform(input(name0, sort(1), pair(3, identity, sort(0)), 128)))
    .expect(safety and s.environment.nth(0).value == pair(3, identity, sort(0)) and s.environment.nth(0).inferred == sort(1))
  run betaDeclaredTypeRetainedTest = init.then(perform(input(name0,
      pair(3, pair(4, sort(2), variable(0)), sort(1)), sort(0), 128)))
    .expect(safety and s.environment.nth(0).ty.nth(0) == 3 and s.environment.nth(0).inferred == sort(1))
  run zetaValueRetainedTest = init.then(perform(input(name0, sort(1), letExpr(sort(1), sort(0), variable(0)), 128)))
    .expect(safety and s.environment.nth(0).value.nth(0) == 6 and s.environment.nth(0).inferred == sort(1))
  run zetaDeclaredTypeRetainedTest = init.then(perform(input(name0, letExpr(sort(2), sort(1), variable(0)), sort(0), 128)))
    .expect(safety and s.environment.nth(0).ty.nth(0) == 6 and s.environment.nth(0).inferred == sort(1))
  run storedAliasNormalizationTest = init.then(perform(input(name0, sort(2), sort(1), 128)))
    .then(perform(input(name1, pair(5, constant(name0), constant(name0)), pair(4, constant(name0), variable(0)), 128)))
    .expect(safety and s.environment.nth(1).ty == pair(5, constant(name0), constant(name0))
      and s.environment.nth(1).inferred == identityType)
  run constantUsesDeclaredTypeTest = init.then(perform(input(name0, sort(2), sort(1), 128)))
    .then(perform(input(name1, pair(5, constant(name0), constant(name0)), pair(4, constant(name0), variable(0)), 128)))
    .expect(safety and eval(s.environment, 2, constant(name1), List(), List(), 128).value
      == pair(5, constant(name0), constant(name0)))
  run deltaUsesStoredValueTest = init.then(perform(input(name0, sort(2), sort(1), 128)))
    .expect(safety and eval(s.environment, 1, constant(name0), List(), List(), 128) == { value: sort(1), code: 0 })
  run erasedBetaUnknownRefusalTest = init.then(perform(input(name0, sort(1),
      pair(3, pair(4, sort(1), sort(0)), constant(List(122))), 128)))
    .expect(safety and s.snapshots.nth(0).code == 2 and s.environment == List())
  run erasedZetaUnknownRefusalTest = init.then(perform(input(name0, sort(1),
      letExpr(sort(1), constant(List(122)), sort(0)), 128)))
    .expect(safety and s.snapshots.nth(0).code == 2 and s.environment == List())
  run expectedFunctionRefusalTest = init.then(perform(input(name0, sort(1), pair(3, sort(0), sort(0)), 128)))
    .expect(safety and s.snapshots.nth(0).code == 5 and s.environment == List())
  run expectedSortRefusalTest = init.then(perform(input(name0, sort(1), pair(4, identity, variable(0)), 128)))
    .expect(safety and s.snapshots.nth(0).code == 4 and s.environment == List())
  run finalConversionMismatchTest = init.then(perform(input(name0, sort(2), sort(0), 128)))
    .expect(safety and s.snapshots.nth(0).code == 6 and s.environment == List())
  run typedLetMismatchTest = init.then(perform(input(name0, sort(1), letExpr(sort(1), sort(1), variable(0)), 128)))
    .expect(safety and s.snapshots.nth(0).code == 6 and s.environment == List())
  run duplicatePreemptsScopeTest = init.then(perform(defaultInput))
    .then(perform(input(name0, constant(List(122)), variable(0), 0)))
    .expect(safety and s.snapshots.nth(1).code == 3 and s.environment == previous.environment and not(s.halted))
  run scopePreemptsUnknownTest = init.then(perform(input(name0, sort(1), pair(3, constant(List(122)), variable(0)), 128)))
    .expect(safety and s.snapshots.nth(0).code == 1 and s.halted)
  run refusalThenRetryTest = init.then(perform(input(name0, sort(2), sort(0), 128)))
    .then(perform(defaultInput)).expect(safety and s.environment.length() == 1 and s.snapshots.nth(0).code == 6)
  run fatalScopeAbsorbingTest = init.then(perform(input(name0, sort(1), variable(0), 128)))
    .then(perform(defaultInput)).expect(safety and s == previous and s.snapshots.length() == 1)
  run dependentApplicationTest = init.then(perform(input(name0, pair(5, sort(0), sort(0)),
      pair(3, pair(4, sort(1), pair(4, variable(0), variable(0))), sort(0)), 128)))
    .expect(safety and s.environment.nth(0).inferred == pair(5, sort(0), sort(0)))
  run nestedCaptureAvoidanceTest = init.then(perform(input(name0, pair(5, sort(1), identityType),
      pair(4, sort(1), letExpr(sort(1), variable(0), pair(4, sort(1), variable(1)))), 128)))
    .expect(safety and s.environment.nth(0).inferred == pair(5, sort(1), identityType))
  run impredicativePiTest = init.expect(safety and
    eval(List(), 2, pair(5, sort(1), variable(1)), List(), List(sort(0)), 128) == { value: sort(0), code: 0 })
  run modelFuelExhaustionTest = init.then(perform(input(name0, sort(1), sort(0), 0)))
    .expect(safety and s.snapshots.nth(0).code == 9 and s.halted and s.environment == List())
  run headFuelBoundaryTest = init.expect(safety and
    eval(List(), 0, pair(3, identity, sort(0)), List(), List(), 1).code == 9 and
    eval(List(), 0, pair(3, identity, sort(0)), List(), List(), 2) == { value: sort(0), code: 0 })
  run contextLookupLiftsTest = init.expect(safety and
    eval(List(), 2, variable(1), List(), List(sort(1), variable(0)), 128)
      == { value: variable(2), code: 0 })

  // Exact negative witness: overwrite the inferred Pi of a successful identity
  // with Sort 0, including its snapshot. Every original field stays visible.
  action unsafeStep = {
    val query = input(name0, identityType, identity, 128)
    val accepted = advance(initial, query.name, query.ty, query.value, query.fuel)
    val wrong = { ...accepted.environment.nth(0), inferred: sort(0) }
    val corrupted = { ...accepted, environment: List(wrong),
      snapshots: List({ name: query.name, code: 0, bindings: List(wrong) }) }
    all { s' = corrupted, previous' = initial, last' = query, hasStep' = true }
  }
}

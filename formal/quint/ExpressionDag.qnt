// Immutable expression DAG representation and binder scope only. This model
// does not infer types, substitute expressions, normalize, or admit definitions.
// The replay boundary accepts canonical natural-number raw fields and ASCII
// names; the core treats constant name vectors opaquely.
module ExpressionDag {
  type Node = { tag: int, a: int, b: int, c: int, name: List[int] }
  type Row = { expression: List[int], height: int, loose: int }
  type State = {
    nodes: List[Node], rows: List[Row], decoded: bool, acceptance_authority: bool,
  }

  pure def node(tag: int, a: int, b: int, c: int, name: List[int]): Node =
    { tag: tag, a: a, b: b, c: c, name: name }
  pure def leaf(tag: int, payload: int): Node = node(tag, payload, 0, 0, List())
  pure def binary(tag: int, left: int, right: int): Node = node(tag, left, right, 0, List())
  pure def maximum(a: int, b: int): int = if (a > b) a else b
  pure def predecessor(value: int): int = if (value > 0) value - 1 else 0
  pure val initial: State = {
    nodes: List(), rows: List(), decoded: true, acceptance_authority: false,
  }

  // Leaves have no edges. Meaningful child IDs must point strictly backwards;
  // malformed topology is refused before any child lookup is evaluated.
  pure def earlier(id: int, limit: int): bool = id >= 0 and id < limit
  pure def topology(raw: Node, limit: int): bool =
    if (Set(0, 1, 2).contains(raw.tag)) true
    else if (Set(3, 4, 5).contains(raw.tag)) earlier(raw.a, limit) and earlier(raw.b, limit)
    else if (raw.tag == 6) earlier(raw.a, limit) and earlier(raw.b, limit) and earlier(raw.c, limit)
    else false

  // Prefix expression tokens are lossless: sort/var carry one integer;
  // constants carry their byte count and opaque bytes; constructor arities
  // delimit the recursively expanded children without any pointer renaming.
  pure def decodeNode(raw: Node, rows: List[Row]): Row =
    if (raw.tag == 0) { expression: List(0, raw.a), height: 1, loose: 0 }
    else if (raw.tag == 1) { expression: List(1, raw.a), height: 1, loose: raw.a + 1 }
    else if (raw.tag == 2) {
      expression: List(2, raw.name.length()).concat(raw.name), height: 1, loose: 0,
    } else {
      val left = rows.nth(raw.a)
      val right = rows.nth(raw.b)
      if (raw.tag == 6) {
        val body = rows.nth(raw.c)
        {
          expression: List(6).concat(left.expression).concat(right.expression).concat(body.expression),
          height: 1 + maximum(left.height, maximum(right.height, body.height)),
          loose: maximum(left.loose, maximum(right.loose, predecessor(body.loose))),
        }
      } else {
        expression: List(raw.tag).concat(left.expression).concat(right.expression),
        height: 1 + maximum(left.height, right.height),
        loose: maximum(left.loose, if (raw.tag == 3) right.loose else predecessor(right.loose)),
      }
    }
  pure def advance(state: State, raw: Node): State =
    if (not(state.decoded)) state
    else if (topology(raw, state.nodes.length())) {
      ...state, nodes: state.nodes.append(raw), rows: state.rows.append(decodeNode(raw, state.rows)),
    } else { ...state, decoded: false }
  pure def replay(nodes: List[Node]): State = nodes.foldl(initial, (state, raw) => advance(state, raw))
  // An invalid whole DAG has no observable decoded expressions or metadata.
  // The internal valid prefix remains available only for invariant checking.
  pure def observedRows(state: State): List[Row] = if (state.decoded) state.rows else List()
  pure def scoped(row: Row, depths: List[int]): List[bool] =
    depths.foldl(List(), (result, depth) => result.append(row.loose <= depth))
  pure def nodePrefix(old: List[Node], current: List[Node]): bool =
    old.length() <= current.length() and old.indices().forall(i => old.nth(i) == current.nth(i))
  pure def rowPrefix(old: List[Row], current: List[Row]): bool =
    old.length() <= current.length() and old.indices().forall(i => old.nth(i) == current.nth(i))
  pure def stateSafety(state: State): bool = all {
    not(state.acceptance_authority), state.nodes.length() == state.rows.length(),
    state.nodes.indices().forall(i => topology(state.nodes.nth(i), i) and
      state.rows.nth(i) == decodeNode(state.nodes.nth(i), state.rows)),
    state.rows.indices().forall(i => state.rows.nth(i).height >= 1 and state.rows.nth(i).loose >= 0),
  }

  var s: State
  var previous: State
  var last: Node
  var hasStep: bool
  action init = all {
    s' = initial, previous' = initial, last' = leaf(0, 0), hasStep' = false,
  }
  action perform(raw: Node): bool = all {
    s' = advance(s, raw), previous' = s, last' = raw, hasStep' = true,
  }
  // Simulation explores at most eight nodes and then stutters. This explicit
  // arena bound also bounds expansion of shared DAGs into structural wires.
  // All seven tags, payloads 0..3, and every earlier child ID are available.
  pure val simulationNodeBound = 8
  action stutter = all { s' = s, previous' = s, last' = last, hasStep' = false }
  action step = if (s.nodes.length() >= simulationNodeBound) stutter else {
    nondet tag = (if (s.nodes.length() == 0) Set(0, 1, 2) else 0.to(6)).oneOf()
    nondet payload = 0.to(3).oneOf()
    nondet first = (if (s.nodes.length() == 0) Set(0) else 0.to(s.nodes.length() - 1)).oneOf()
    nondet second = (if (s.nodes.length() == 0) Set(0) else 0.to(s.nodes.length() - 1)).oneOf()
    nondet third = (if (s.nodes.length() == 0) Set(0) else 0.to(s.nodes.length() - 1)).oneOf()
    val raw = if (tag == 2) node(2, 0, 0, 0, List(110, 48 + payload))
              else if (tag < 2) leaf(tag, payload)
              else if (tag == 6) node(6, first, second, third, List())
              else binary(tag, first, second)
    perform(raw)
  }
  val immutablePrefix = hasStep implies
    nodePrefix(previous.nodes, s.nodes) and rowPrefix(previous.rows, s.rows)
  val refusalAtomicity = (hasStep and previous.decoded and not(topology(last, previous.nodes.length())))
    implies not(s.decoded) and s.nodes == previous.nodes and s.rows == previous.rows
  val refusedAbsorbing = (hasStep and not(previous.decoded)) implies s == previous
  val safety = stateSafety(s) and immutablePrefix and refusalAtomicity and refusedAbsorbing

  // Replay adapters serialize data literals only. Quint returns the exact
  // request identity followed by length-framed independently computed results.
  pure def vectorWire(values: List[int]): List[int] = List(values.length()).concat(values)
  pure def nodeWire(raw: Node): List[int] = List(raw.tag, raw.a, raw.b, raw.c).concat(vectorWire(raw.name))
  pure def identityWire(id: int, nodes: List[Node], depths: List[int]): List[int] =
    List(id, nodes.length()).concat(nodes.foldl(List(), (result, raw) => result.concat(nodeWire(raw))))
      .concat(vectorWire(depths))
  pure def resultWire(state: State, depths: List[int]): List[int] = {
    val rows = observedRows(state)
    List(if (state.decoded) 1 else 0, if (state.acceptance_authority) 1 else 0, rows.length())
      .concat(rows.foldl(List(), (result, row) => result.concat(vectorWire(row.expression))
        .concat(List(row.height, row.loose, depths.length()))
        .concat(depths.foldl(List(), (bits, depth) => bits.append(if (row.loose <= depth) 1 else 0)))))
  }
  pure def replayRequest(id: int, nodes: List[Node], depths: List[int]): List[int] =
    identityWire(id, nodes, depths).concat(resultWire(replay(nodes), depths))

  run emptyDagTest = init.expect(safety and s.decoded and observedRows(s) == List())
  run leafPayloadsTest = init.then(perform(leaf(0, 3))).then(perform(leaf(1, 2)))
    .then(perform(node(2, 0, 0, 0, List(110, 48))))
    .expect(safety and s.rows == List(
      { expression: List(0, 3), height: 1, loose: 0 },
      { expression: List(1, 2), height: 1, loose: 3 },
      { expression: List(2, 2, 110, 48), height: 1, loose: 0 }))
  run applicationDecodeTest = init.then(perform(leaf(0, 0))).then(perform(leaf(1, 1)))
    .then(perform(binary(3, 0, 1)))
    .expect(safety and s.rows.nth(2) == { expression: List(3, 0, 0, 1, 1), height: 2, loose: 2 })
  run lambdaBinderTest = init.then(perform(leaf(0, 0))).then(perform(leaf(1, 0)))
    .then(perform(binary(4, 0, 1)))
    .expect(safety and s.rows.nth(2) == { expression: List(4, 0, 0, 1, 0), height: 2, loose: 0 })
  run piBinderTest = init.then(perform(leaf(0, 0))).then(perform(leaf(1, 0)))
    .then(perform(binary(5, 0, 1)))
    .expect(safety and s.rows.nth(2) == { expression: List(5, 0, 0, 1, 0), height: 2, loose: 0 })
  run letBinderTest = init.then(perform(leaf(0, 0))).then(perform(leaf(1, 0)))
    .then(perform(node(6, 0, 0, 1, List())))
    .expect(safety and s.rows.nth(2) == { expression: List(6, 0, 0, 0, 0, 1, 0), height: 2, loose: 0 })
  run openDomainNotBoundTest = init.then(perform(leaf(1, 0))).then(perform(binary(4, 0, 0)))
    .expect(safety and s.rows.nth(1).loose == 1 and scoped(s.rows.nth(1), List(0, 1)) == List(false, true))
  run letValueNotBoundTest = init.then(perform(leaf(0, 0))).then(perform(leaf(1, 0)))
    .then(perform(node(6, 0, 1, 1, List())))
    .expect(safety and s.rows.nth(2).loose == 1 and scoped(s.rows.nth(2), List(0)) == List(false))
  run nestedBinderDecrementTest = init.then(perform(leaf(0, 0))).then(perform(leaf(1, 1)))
    .then(perform(binary(4, 0, 1))).then(perform(binary(5, 0, 2)))
    .expect(safety and s.rows.nth(2).loose == 1 and s.rows.nth(3).loose == 0 and s.rows.nth(3).height == 3)
  run sharedOpenSubtreeDepthTest = init.then(perform(leaf(0, 0))).then(perform(leaf(1, 1)))
    .then(perform(binary(4, 0, 1))).then(perform(binary(4, 0, 2))).then(perform(binary(3, 2, 3)))
    .expect(safety and scoped(s.rows.nth(1), List(0, 1, 2, 3)) == List(false, false, true, true) and
      scoped(s.rows.nth(2), List(0, 1, 2, 3)) == List(false, true, true, true) and
      scoped(s.rows.nth(3), List(0, 1, 2, 3)) == List(true, true, true, true) and s.rows.nth(4).loose == 1)
  run selfReferenceRefusalTest = init.then(perform(leaf(0, 0))).then(perform(binary(3, 0, 1)))
    .expect(safety and not(s.decoded) and observedRows(s) == List() and s.rows == previous.rows)
  run forwardReferenceRefusalTest = init.then(perform(binary(4, 1, 1)))
    .expect(safety and not(s.decoded) and s.rows == List())
  run escapingReferenceRefusalTest = init.then(perform(leaf(0, 0))).then(perform(node(6, 0, 0, 99, List())))
    .expect(safety and not(s.decoded) and observedRows(s) == List())
  run cyclicReferenceRefusalTest = init.then(perform(binary(3, 1, 1))).then(perform(binary(3, 0, 0)))
    .expect(safety and not(s.decoded) and s.nodes == List() and s.rows == List())
  run snapshotPrefixPreservedTest = init.then(perform(leaf(0, 0))).then(perform(leaf(1, 2)))
    .then(perform(binary(4, 0, 1))).then(perform(binary(3, 2, 2)))
    .expect(safety and s.rows.slice(0, 3) == previous.rows and s.nodes.slice(0, 3) == previous.nodes)
  run refusedDagHasNoExpressionsTest = init.then(perform(leaf(0, 1))).then(perform(binary(5, 0, 3)))
    .expect(safety and resultWire(s, List(0, 1, 2, 3)) == List(0, 0, 0))
  run scopeDepthMonotoneTest = init.then(perform(leaf(1, 2)))
    .expect(safety and scoped(s.rows.nth(0), List(0, 1, 2, 3, 4)) == List(false, false, false, true, true))
  run exactHeightTest = init.then(perform(leaf(0, 0))).then(perform(binary(3, 0, 0)))
    .then(perform(binary(4, 0, 1))).then(perform(node(6, 0, 2, 1, List())))
    .expect(safety and s.rows.nth(3).height == 4 and s.rows.nth(3).loose == 0)
  run constantNamesLosslessTest = init.then(perform(node(2, 0, 0, 0, List(97))))
    .then(perform(node(2, 0, 0, 0, List(97, 98))))
    .expect(safety and s.rows.nth(0).expression == List(2, 1, 97) and
      s.rows.nth(1).expression == List(2, 2, 97, 98) and s.rows.nth(0).expression != s.rows.nth(1).expression)
  run dagAuthorityPreservedTest = init.then(perform(leaf(0, 0))).then(perform(leaf(1, 0)))
    .then(perform(binary(4, 0, 1)))
    .expect(safety and not(s.acceptance_authority))
  run simulationBoundStuttersTest = init.then(perform(leaf(0, 0))).then(perform(leaf(0, 1)))
    .then(perform(leaf(0, 2))).then(perform(leaf(0, 3))).then(perform(leaf(1, 0)))
    .then(perform(leaf(1, 1))).then(perform(leaf(1, 2))).then(perform(leaf(1, 3))).then(step)
    .expect(safety and s.nodes.length() == simulationNodeBound and s == previous)

  // A reachable two-leaf prefix followed by one deliberately incorrect binder
  // decrement. Var 1 under one binder remains open, but this action reports
  // loose=0 and hence would incorrectly report closedness at depth zero.
  pure val unsafeStart = replay(List(leaf(0, 0), leaf(1, 1)))
  action unsafeInit = all {
    s' = unsafeStart, previous' = unsafeStart, last' = leaf(1, 1), hasStep' = false,
  }
  action unsafeStep = {
    val raw = binary(4, 0, 1)
    val accepted = advance(s, raw)
    val index = accepted.rows.length() - 1
    val body = s.rows.nth(1)
    val wrong = { ...accepted.rows.nth(index), loose: maximum(s.rows.nth(0).loose,
      if (body.loose >= 2) body.loose - 2 else 0) }
    all {
      s' = { ...accepted, rows: accepted.rows.replaceAt(index, wrong) },
      previous' = s, last' = raw, hasStep' = true,
    }
  }
}

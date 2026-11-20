// Independent structural lift and capture-avoiding substitution. The adapter
// supplies canonical natural-number raw fields and valid operation arguments.
// This model neither checks types nor reduces expressions nor admits bindings.
module Substitution {
  type Node = { tag: int, a: int, b: int, c: int, name: List[int] }
  type Row = { expression: List[int], height: int, loose: int }
  type Plan = { row: Row, shifted: List[bool], cutoff: int }
  type Request = {
    nodes: List[Node], operation: int, root: int, parameter: int, cutoff: int,
  }
  type Observation = { decoded: bool, rows: List[Row], acceptance_authority: bool }

  pure def node(tag: int, a: int, b: int, c: int, name: List[int]): Node =
    { tag: tag, a: a, b: b, c: c, name: name }
  pure def leaf(tag: int, payload: int): Node = node(tag, payload, 0, 0, List())
  pure def binary(tag: int, left: int, right: int): Node = node(tag, left, right, 0, List())
  pure def request(nodes: List[Node], operation: int, root: int, parameter: int, cutoff: int): Request =
    { nodes: nodes, operation: operation, root: root, parameter: parameter, cutoff: cutoff }
  pure def maximum(a: int, b: int): int = if (a > b) a else b
  pure def predecessor(value: int): int = if (value > 0) value - 1 else 0
  pure def earlier(id: int, limit: int): bool = id >= 0 and id < limit
  pure def topology(raw: Node, limit: int): bool =
    if (Set(0, 1, 2).contains(raw.tag)) true
    else if (Set(3, 4, 5).contains(raw.tag)) earlier(raw.a, limit) and earlier(raw.b, limit)
    else if (raw.tag == 6) earlier(raw.a, limit) and earlier(raw.b, limit) and earlier(raw.c, limit)
    else false
  pure def validDag(nodes: List[Node]): bool =
    nodes.indices().forall(i => topology(nodes.nth(i), i))

  pure def leafRow(raw: Node): Row =
    if (raw.tag == 0) { expression: List(0, raw.a), height: 1, loose: 0 }
    else if (raw.tag == 1) { expression: List(1, raw.a), height: 1, loose: raw.a + 1 }
    else { expression: List(2, raw.name.length()).concat(raw.name), height: 1, loose: 0 }
  pure def joinRows(tag: int, left: Row, right: Row, body: Row): Row =
    if (tag == 6) {
      expression: List(6).concat(left.expression).concat(right.expression).concat(body.expression),
      height: 1 + maximum(left.height, maximum(right.height, body.height)),
      loose: maximum(left.loose, maximum(right.loose, predecessor(body.loose))),
    } else {
      expression: List(tag).concat(left.expression).concat(right.expression),
      height: 1 + maximum(left.height, right.height),
      loose: maximum(left.loose, if (tag == 3) right.loose else predecessor(right.loose)),
    }
  pure def falseMask(values: List[int]): List[bool] =
    values.foldl(List(), (result, ignored) => result.append(false))

  // A lift plan marks only eligible variable-index payloads, never tags,
  // levels, name lengths, or name bytes. Its cutoff is local to this subtree.
  pure def planAt(raw: Node, table: List[List[Plan]], base: int, offset: int): Plan = {
    val cutoff = base + offset
    if (raw.tag <= 2) {
      val row = leafRow(raw)
      { row: row, cutoff: cutoff,
        shifted: if (raw.tag == 1) List(false, raw.a >= cutoff) else falseMask(row.expression) }
    } else {
      val left = table.nth(raw.a).nth(offset)
      val right = table.nth(raw.b).nth(offset + (if (Set(4, 5).contains(raw.tag)) 1 else 0))
      val body = if (raw.tag == 6) table.nth(raw.c).nth(offset + 1) else left
      {
        row: joinRows(raw.tag, left.row, right.row, body.row), cutoff: cutoff,
        shifted: List(false).concat(left.shifted).concat(right.shifted)
          .concat(if (raw.tag == 6) body.shifted else List()),
      }
    }
  }

  // For an N-node DAG, row i has offsets 0..N-1-i. Every child j<i has
  // a strictly longer row, so both offset and offset+1 are available. This
  // triangular table covers every possible binder path in the supplied DAG.
  // The bound depends on node count, never on a numeric index or cutoff.
  // There is no fuel-exhaustion branch that could fabricate a successful row.
  pure def planTable(nodes: List[Node], cutoff: int): List[List[Plan]] =
    nodes.foldl(List(), (table, raw) => table.append(
      nodes.slice(table.length(), nodes.length()).foldl(List(), (row, ignored) =>
        row.append(planAt(raw, table, cutoff, row.length())))))

  pure def applyPlan(plan: Plan, amount: int): Row = {
    expression: plan.row.expression.foldl(List(), (result, token) =>
      result.append(token + (if (plan.shifted.nth(result.length())) amount else 0))),
    height: plan.row.height,
    // A free-variable requirement above the cutoff increases by amount;
    // lower requirements are untouched. The maximum therefore follows this
    // exact equation, including closed expressions and amount zero.
    loose: if (plan.row.loose <= plan.cutoff) plan.row.loose else plan.row.loose + amount,
  }
  pure def liftRoot(nodes: List[Node], root: int, amount: int, cutoff: int): Row =
    applyPlan(planTable(nodes, cutoff).nth(root).nth(0), amount)

  pure def substituteAt(raw: Node, table: List[List[Row]], replacement: Plan,
      base: int, offset: int): Row = {
    val cutoff = base + offset
    if (raw.tag == 1) {
      if (raw.a < cutoff) leafRow(raw)
      else if (raw.a == cutoff) applyPlan(replacement, cutoff)
      else leafRow(leaf(1, raw.a - 1))
    } else if (raw.tag <= 2) leafRow(raw)
    else {
      val left = table.nth(raw.a).nth(offset)
      val right = table.nth(raw.b).nth(offset + (if (Set(4, 5).contains(raw.tag)) 1 else 0))
      val body = if (raw.tag == 6) table.nth(raw.c).nth(offset + 1) else left
      joinRows(raw.tag, left, right, body)
    }
  }
  pure def substitutionTable(nodes: List[Node], replacement: Plan, cutoff: int): List[List[Row]] =
    nodes.foldl(List(), (table, raw) => table.append(
      nodes.slice(table.length(), nodes.length()).foldl(List(), (row, ignored) =>
        row.append(substituteAt(raw, table, replacement, cutoff, row.length())))))
  pure def substituteRoot(nodes: List[Node], root: int, replacement: int, cutoff: int): Row = {
    val plan = planTable(nodes, 0).nth(replacement).nth(0)
    substitutionTable(nodes, plan, cutoff).nth(root).nth(0)
  }

  pure val refused: Observation = { decoded: false, rows: List(), acceptance_authority: false }
  pure def observe(query: Request): Observation =
    if (not(validDag(query.nodes))) refused
    else {
      val row = if (query.operation == 0)
        liftRoot(query.nodes, query.root, query.parameter, query.cutoff)
      else substituteRoot(query.nodes, query.root, query.parameter, query.cutoff)
      { decoded: true, rows: List(row), acceptance_authority: false }
    }
  pure def scoped(row: Row, depths: List[int]): List[bool] =
    depths.foldl(List(), (result, depth) => result.append(row.loose <= depth))

  // The actual evaluator echoes the entire request, including operation
  // arguments, before its independently computed length-framed observation.
  pure def vectorWire(values: List[int]): List[int] = List(values.length()).concat(values)
  pure def nodeWire(raw: Node): List[int] = List(raw.tag, raw.a, raw.b, raw.c).concat(vectorWire(raw.name))
  pure def identityWire(id: int, query: Request, depths: List[int]): List[int] =
    List(id, query.nodes.length())
      .concat(query.nodes.foldl(List(), (result, raw) => result.concat(nodeWire(raw))))
      .concat(List(query.operation, query.root, query.parameter, query.cutoff)).concat(vectorWire(depths))
  pure def resultWire(observation: Observation, depths: List[int]): List[int] =
    List(if (observation.decoded) 1 else 0, if (observation.acceptance_authority) 1 else 0,
      observation.rows.length())
      .concat(observation.rows.foldl(List(), (result, row) => result.concat(vectorWire(row.expression))
        .concat(List(row.height, row.loose, depths.length()))
        .concat(depths.foldl(List(), (bits, depth) => bits.append(if (row.loose <= depth) 1 else 0)))))
  pure def replayRequest(id: int, nodes: List[Node], operation: int, root: int,
      parameter: int, cutoff: int, depths: List[int]): List[int] = {
    val query = request(nodes, operation, root, parameter, cutoff)
    identityWire(id, query, depths).concat(resultWire(observe(query), depths))
  }

  var q: Request
  var observed: Observation
  pure val initialQuery = request(List(leaf(0, 0)), 0, 0, 0, 0)
  action init = all { q' = initialQuery, observed' = observe(initialQuery) }
  action perform(query: Request): bool = all { q' = query, observed' = observe(query) }
  pure val simulationNodeBound = 6
  action stutter = all { q' = q, observed' = observed }
  // Bounded exploration: at most six nodes, all seven tags, payloads 0..3,
  // every earlier child/root/replacement ID, both operations and cutoffs 0..3.
  action step = if (q.nodes.length() >= simulationNodeBound) stutter else {
    nondet tag = 0.to(6).oneOf()
    nondet payload = 0.to(3).oneOf()
    nondet first = 0.to(q.nodes.length() - 1).oneOf()
    nondet second = 0.to(q.nodes.length() - 1).oneOf()
    nondet third = 0.to(q.nodes.length() - 1).oneOf()
    nondet operation = 0.to(1).oneOf()
    nondet root = 0.to(q.nodes.length()).oneOf()
    nondet replacement = 0.to(q.nodes.length()).oneOf()
    nondet amount = 0.to(3).oneOf()
    nondet cutoff = 0.to(3).oneOf()
    val raw = if (tag == 2) node(2, 0, 0, 0, List(110, 48 + payload))
      else if (tag < 2) leaf(tag, payload)
      else if (tag == 6) node(6, first, second, third, List())
      else binary(tag, first, second)
    perform(request(q.nodes.append(raw), operation, root,
      if (operation == 0) amount else replacement, cutoff))
  }

  pure def operationSafety(query: Request, result: Observation): bool = {
    if (not(validDag(query.nodes))) result == refused
    else {
      val originals = planTable(query.nodes, 0)
      val source = originals.nth(query.root).nth(0).row
      val row = result.rows.nth(0)
      all {
        result.decoded, result.rows.length() == 1, row.height >= 1, row.loose >= 0,
        (source.loose <= query.cutoff) implies row == source,
        if (query.operation == 0) all {
          row.height == source.height,
          row.loose <= source.loose + query.parameter,
          (query.parameter == 0) implies row == source,
        } else {
          val replacement = originals.nth(query.parameter).nth(0).row
          all {
            row.height <= source.height + replacement.height - 1,
            row.loose <= maximum(query.cutoff,
              maximum(predecessor(source.loose), query.cutoff + replacement.loose)),
            (source.loose <= 1 and query.cutoff == 0 and replacement.loose == 0) implies row.loose == 0,
          }
        },
      }
    }
  }
  val safety = not(observed.acceptance_authority) and observed == observe(q) and operationSafety(q, observed)

  pure val leaves = List(leaf(0, 3), leaf(1, 0), leaf(1, 1), leaf(1, 2),
    node(2, 0, 0, 0, List(97, 95, 49)))
  run liftZeroTest = init.then(perform(request(leaves.append(binary(3, 2, 4)), 0, 5, 0, 0)))
    .expect(safety and observed.rows.nth(0).expression == List(3, 1, 1, 2, 3, 97, 95, 49))
  run liftBelowCutoffTest = init.then(perform(request(leaves, 0, 1, 3, 1)))
    .expect(safety and observed.rows.nth(0) == leafRow(leaf(1, 0)))
  run liftAtCutoffTest = init.then(perform(request(leaves, 0, 2, 3, 1)))
    .expect(safety and observed.rows.nth(0) == leafRow(leaf(1, 4)))
  run liftAboveCutoffTest = init.then(perform(request(leaves, 0, 3, 3, 1)))
    .expect(safety and observed.rows.nth(0) == leafRow(leaf(1, 5)))
  run sortPayloadUnchangedTest = init.then(perform(request(leaves, 0, 0, 7, 0)))
    .expect(safety and observed.rows.nth(0) == leafRow(leaf(0, 3)))
  run constantNameUnchangedTest = init.then(perform(request(leaves, 1, 4, 1, 0)))
    .expect(safety and observed.rows.nth(0).expression == List(2, 3, 97, 95, 49))
  run applicationBothChildrenTest = init.then(perform(request(leaves.append(binary(3, 2, 3)), 0, 5, 2, 1)))
    .expect(safety and observed.rows.nth(0).expression == List(3, 1, 3, 1, 4))
  run lambdaDomainAndBodyTest = init.then(perform(request(leaves.append(binary(4, 1, 1)), 0, 5, 2, 0)))
    .expect(safety and observed.rows.nth(0).expression == List(4, 1, 2, 1, 0))
  run piDomainAndBodyTest = init.then(perform(request(leaves.append(binary(5, 1, 1)), 0, 5, 2, 0)))
    .expect(safety and observed.rows.nth(0).expression == List(5, 1, 2, 1, 0))
  run letValueAndBodyTest = init.then(perform(request(leaves.append(node(6, 1, 1, 1, List())), 0, 5, 2, 0)))
    .expect(safety and observed.rows.nth(0).expression == List(6, 1, 2, 1, 2, 1, 0))
  run substituteBelowCutoffTest = init.then(perform(request(leaves, 1, 1, 4, 1)))
    .expect(safety and observed.rows.nth(0) == leafRow(leaf(1, 0)))
  run substituteAtCutoffTest = init.then(perform(request(leaves, 1, 2, 1, 1)))
    .expect(safety and observed.rows.nth(0) == leafRow(leaf(1, 1)))
  run substituteAboveCutoffTest = init.then(perform(request(leaves, 1, 3, 4, 1)))
    .expect(safety and observed.rows.nth(0) == leafRow(leaf(1, 1)))
  run substituteApplicationTest = init.then(perform(request(leaves.append(binary(3, 1, 2)), 1, 5, 4, 0)))
    .expect(safety and observed.rows.nth(0).expression == List(3, 2, 3, 97, 95, 49, 1, 0))
  run lambdaAvoidsCaptureTest = init.then(perform(request(leaves.append(binary(4, 0, 2)), 1, 5, 1, 0)))
    .expect(safety and observed.rows.nth(0) == { expression: List(4, 0, 3, 1, 1), height: 2, loose: 1 })
  run piAvoidsCaptureTest = init.then(perform(request(leaves.append(binary(5, 0, 2)), 1, 5, 1, 0)))
    .expect(safety and observed.rows.nth(0) == { expression: List(5, 0, 3, 1, 1), height: 2, loose: 1 })
  run letAvoidsCaptureTest = init.then(perform(request(leaves.append(node(6, 0, 1, 2, List())), 1, 5, 1, 0)))
    .expect(safety and observed.rows.nth(0) == { expression: List(6, 0, 3, 1, 0, 1, 1), height: 2, loose: 1 })
  run nestedBindersAvoidCaptureTest = init.then(perform(request(
      leaves.append(binary(4, 0, 3)).append(binary(5, 0, 5)), 1, 6, 1, 0)))
    .expect(safety and observed.rows.nth(0) == { expression: List(5, 0, 3, 4, 0, 3, 1, 2), height: 3, loose: 1 })
  run replacementOwnBinderTest = init.then(perform(request(
      leaves.append(binary(4, 1, 1)), 1, 2, 5, 1)))
    .expect(safety and observed.rows.nth(0) == { expression: List(4, 1, 1, 1, 0), height: 2, loose: 2 })
  run sharedNodeDifferentDepthsTest = init.then(perform(request(
      leaves.append(binary(4, 0, 2)).append(binary(3, 2, 5)), 1, 6, 1, 0)))
    .expect(safety and observed.rows.nth(0).expression == List(3, 1, 0, 4, 0, 3, 1, 1))
  run selectedRootNotLastTest = init.then(perform(request(
      leaves.append(binary(3, 2, 3)), 0, 2, 2, 0)))
    .expect(safety and observed.rows.nth(0) == leafRow(leaf(1, 3)))
  run hugeCutoffDoesNotBoundTraversalTest = init.then(perform(request(
      leaves.append(binary(4, 1, 2)), 0, 5, 2, 1000000000)))
    .expect(safety and observed.rows.nth(0).expression == List(4, 1, 0, 1, 1))
  run closedSubstitutionResultTest = init.then(perform(request(
      leaves.append(binary(4, 0, 2)), 1, 5, 4, 0)))
    .expect(safety and observed.rows.nth(0).loose == 0 and scoped(observed.rows.nth(0), List(0, 2, 0)) == List(true, true, true))
  run emptyDepthQueriesTest = init.then(perform(request(leaves, 0, 3, 1, 0)))
    .expect(safety and scoped(observed.rows.nth(0), List()) == List())
  run selfReferenceRefusalTest = init.then(perform(request(List(leaf(0, 0), binary(3, 0, 1)), 0, 0, 0, 0)))
    .expect(safety and observed == refused)
  run forwardReferenceRefusalTest = init.then(perform(request(List(binary(4, 1, 1), leaf(0, 0)), 1, 1, 1, 0)))
    .expect(safety and observed == refused)
  run unusedInvalidSuffixRefusalTest = init.then(perform(request(List(leaf(0, 0), node(6, 0, 0, 99, List())), 0, 0, 0, 0)))
    .expect(safety and resultWire(observed, List(0, 1)) == List(0, 0, 0))
  run authorityPreservedTest = init.then(perform(request(leaves, 1, 1, 4, 0)))
    .expect(safety and not(observed.acceptance_authority))
  run triangularRowsCoverAllContextsTest = init.expect({
    val nodes = leaves.append(binary(4, 0, 2)).append(binary(5, 0, 5))
    val plans = planTable(nodes, 0)
    plans.indices().forall(i => plans.nth(i).length() == nodes.length() - i and
      plans.nth(i).indices().forall(j => plans.nth(i).nth(j).shifted.length() == plans.nth(i).nth(j).row.expression.length()))
  })
  run simulationBoundStuttersTest = init.then(perform(request(
      leaves.append(binary(4, 0, 2)), 1, 5, 1, 0))).then(step)
    .expect(safety and q.nodes.length() == simulationNodeBound)

  // Exact reachable negative witness: replacing Var 1 under one lambda with
  // open Var 0 must produce Var 1, preserving its free-variable requirement.
  // The deliberately wrong action inserts unlifted Var 0 and captures it.
  pure val unsafeQuery = request(List(leaf(0, 0), leaf(1, 0), leaf(1, 1), binary(4, 0, 2)), 1, 3, 1, 0)
  action unsafeInit = all { q' = unsafeQuery, observed' = observe(unsafeQuery) }
  action unsafeStep = all {
    q' = q,
    observed' = { decoded: true, acceptance_authority: false,
      rows: List({ expression: List(4, 0, 0, 1, 0), height: 2, loose: 0 }) },
  }
}

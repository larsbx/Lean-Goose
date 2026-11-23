// Bounded checks for the semantic history of a transparent environment.
// Each insertion retains its exact predecessor and original stored fields.
// These finite witnesses use the existing Quint semantic operators separately;
// neither T::check nor equality with T::advance defines certificate validity.
// The arbitrary-environment theorems and relational evidence belong to Lean.
module SemanticEnvironment {
  import TypingConversion as T from "./TypingConversion"
  import StoredBindings as B from "./StoredBindings"

  type Certificate = {
    predecessor: List[T::Binding], stored: T::Binding, fuel: int,
    declaredSort: T::Result, valueType: T::Result, normalizedType: T::Result,
    inferredNormal: T::Result, declaredNormal: T::Result,
  }
  type State = { checked: T::State, certificates: List[Certificate] }

  pure def afterResult(env: List[T::Binding], op: int, input: T::Result, fuel: int): T::Result =
    if (input.code != 0) input else T::eval(env, op, input.value, List(), List(), fuel)
  pure def certificate(env: List[T::Binding], binding: T::Binding, fuel: int): Certificate = {
    val declaredSort = T::eval(env, 3, binding.ty, List(), List(), fuel)
    val valueType = T::eval(env, 2, binding.value, List(), List(), fuel)
    {
      predecessor: env, stored: binding, fuel: fuel,
      declaredSort: declaredSort, valueType: valueType,
      normalizedType: afterResult(env, 1, valueType, fuel),
      inferredNormal: T::eval(env, 1, binding.inferred, List(), List(), fuel),
      declaredNormal: T::eval(env, 1, binding.ty, List(), List(), fuel),
    }
  }

  // The witness equations are evaluated in the PREDECESSOR, before this
  // binding exists. This rejects self-support, forward support, and replacement
  // of the stored fields after a successful original insertion.
  pure def certificateValid(c: Certificate): bool = all {
    T::lookup(c.predecessor, c.stored.name).length() == 0,
    T::closed(c.stored.ty), T::closed(c.stored.value), T::closed(c.stored.inferred),
    T::known(c.predecessor, c.stored.ty), T::known(c.predecessor, c.stored.value),
    T::known(c.predecessor, c.stored.inferred),
    c.declaredSort == T::eval(c.predecessor, 3, c.stored.ty, List(), List(), c.fuel),
    c.declaredSort.code == 0,
    c.valueType == T::eval(c.predecessor, 2, c.stored.value, List(), List(), c.fuel),
    c.valueType.code == 0,
    c.normalizedType == afterResult(c.predecessor, 1, c.valueType, c.fuel),
    c.normalizedType.code == 0, c.normalizedType.value == c.stored.inferred,
    c.inferredNormal == T::eval(c.predecessor, 1, c.stored.inferred, List(), List(), c.fuel),
    c.declaredNormal == T::eval(c.predecessor, 1, c.stored.ty, List(), List(), c.fuel),
    c.inferredNormal.code == 0, c.declaredNormal.code == 0,
    c.inferredNormal.value == c.stored.inferred,
    c.inferredNormal.value == c.declaredNormal.value,
  }

  // A concrete diagnostic name projection. Starting with a nonzero sentinel
  // avoids leading-zero ambiguity. The finite tests use only ASCII name bytes.
  // Lean's generic projection theorem assumes an injective naming function;
  // this Quint sample is not a proof of that assumption for every byte vector.
  pure def nameKey(name: List[int]): int = name.foldl(1, (key, byte) => 257 * key + byte)
  pure def project(binding: T::Binding): B::Binding = {
    name: nameKey(binding.name), ty: binding.ty, value: binding.value, inferred: binding.inferred,
  }
  pure def projectEnvironment(environment: List[T::Binding]): List[B::Binding] =
    environment.foldl(List(), (result, binding) => result.append(project(binding)))
  pure def lookupProjects(environment: List[T::Binding], name: List[int]): bool =
    B::lookup(projectEnvironment(environment), nameKey(name))
      == projectEnvironment(T::lookup(environment, name))
  pure def recordsMatch(state: State): bool =
    state.certificates.length() == state.checked.environment.length() and
    state.certificates.indices().forall(i => {
      val c = state.certificates.nth(i)
      all {
        c.predecessor == state.checked.environment.slice(0, i),
        c.stored == state.checked.environment.nth(i),
        certificateValid(c),
      }
    })
  pure def uniqueNames(environment: List[T::Binding]): bool =
    environment.indices().forall(i => environment.indices().forall(j =>
      i == j or environment.nth(i).name != environment.nth(j).name))
  pure def projectionSafety(environment: List[T::Binding]): bool = all {
    projectEnvironment(environment).length() == environment.length(),
    environment.indices().forall(i => {
      val b = environment.nth(i)
      val p = projectEnvironment(environment).nth(i)
      all { p.name == nameKey(b.name), p.ty == b.ty, p.value == b.value, p.inferred == b.inferred,
        lookupProjects(environment, b.name) }
    }),
    environment.indices().forall(i => environment.indices().forall(j =>
      i == j or nameKey(environment.nth(i).name) != nameKey(environment.nth(j).name))),
  }
  pure def remainsValidIn(c: Certificate, environment: List[T::Binding]): bool = all {
    T::known(environment, c.stored.ty), T::known(environment, c.stored.value),
    T::known(environment, c.stored.inferred),
    T::eval(environment, 3, c.stored.ty, List(), List(), c.fuel) == c.declaredSort,
    T::eval(environment, 2, c.stored.value, List(), List(), c.fuel) == c.valueType,
    afterResult(environment, 1, c.valueType, c.fuel) == c.normalizedType,
    T::eval(environment, 1, c.stored.inferred, List(), List(), c.fuel) == c.inferredNormal,
    T::eval(environment, 1, c.stored.ty, List(), List(), c.fuel) == c.declaredNormal,
  }
  pure def semanticHistorySafety(state: State): bool = all {
    T::stateSafety(state.checked), uniqueNames(state.checked.environment), recordsMatch(state),
    projectionSafety(state.checked.environment),
    state.certificates.indices().forall(i => remainsValidIn(state.certificates.nth(i), state.checked.environment)),
  }

  pure val initial: State = { checked: T::initial, certificates: List() }
  pure def advance(state: State, query: T::Input): State =
    if (state.checked.halted) state else {
      val checkedNext = T::advance(state.checked, query.name, query.ty, query.value, query.fuel)
      val appended = checkedNext.environment.length() == state.checked.environment.length() + 1
      {
        checked: checkedNext,
        certificates: if (appended) state.certificates.append(certificate(state.checked.environment,
          checkedNext.environment.nth(checkedNext.environment.length() - 1), query.fuel)) else state.certificates,
      }
    }
  pure def replay(queries: List[T::Input]): State = queries.foldl(initial, (state, query) => advance(state, query))

  pure val U = List(85)
  pure val identityName = List(105, 100)
  pure val aliasName = List(86)
  pure val typeAlias = T::input(U, T::sort(2), T::sort(1), 128)
  pure val identityAlias = T::input(identityName,
    T::pair(5, T::constant(U), T::constant(U)), T::pair(4, T::constant(U), T::variable(0)), 128)
  pure val valueAlias = T::input(aliasName, T::sort(2), T::constant(U), 128)
  pure val sampleNames = List(U, identityName, aliasName, List(120), List(122), List(65), List(65, 65))

  var s: State
  var previous: State
  var last: T::Input
  var hasStep: bool
  action init = all { s' = initial, previous' = initial, last' = typeAlias, hasStep' = false }
  action perform(query: T::Input): bool = all {
    s' = advance(s, query), previous' = s, last' = query, hasStep' = true,
  }
  val oldRecordsPreserved = if (not(hasStep)) true else all {
    T::prefix(previous.checked.environment, s.checked.environment),
    previous.certificates.length() <= s.certificates.length(),
    previous.certificates.indices().forall(i => previous.certificates.nth(i) == s.certificates.nth(i)),
    previous.checked.environment.indices().forall(i => {
      val name = previous.checked.environment.nth(i).name
      T::lookup(previous.checked.environment, name) == T::lookup(s.checked.environment, name)
    }),
    B::prefix(projectEnvironment(previous.checked.environment), projectEnvironment(s.checked.environment)),
  }
  val refusalPreservesHistory = if (not(hasStep) or previous.checked.halted) true
    else {
      val latest = s.checked.snapshots.nth(s.checked.snapshots.length() - 1)
      latest.code != 0 implies all {
        s.checked.environment == previous.checked.environment,
        s.certificates == previous.certificates,
      }
    }
  val exactInsertion = if (not(hasStep) or previous.checked.halted) true else {
    val latest = s.checked.snapshots.nth(s.checked.snapshots.length() - 1)
    latest.code == 0 implies all {
      s.checked.environment.length() == previous.checked.environment.length() + 1,
      latest.name == last.name,
      s.checked.environment.nth(previous.checked.environment.length()).name == last.name,
      s.checked.environment.nth(previous.checked.environment.length()).ty == last.ty,
      s.checked.environment.nth(previous.checked.environment.length()).value == last.value,
    }
  }
  val haltedAbsorbing = (hasStep and previous.checked.halted) implies s == previous
  val safety = semanticHistorySafety(s) and oldRecordsPreserved and refusalPreservesHistory
    and exactInsertion and haltedAbsorbing and sampleNames.indices().forall(i => lookupProjects(s.checked.environment, sampleNames.nth(i)))

  pure val simulationSnapshotBound = 4
  action stutter = all { s' = s, previous' = previous, last' = last, hasStep' = hasStep }
  action step = if (s.checked.snapshots.length() >= simulationSnapshotBound) stutter else {
    nondet kind = 0.to(8).oneOf()
    nondet name = Set(U, identityName, aliasName).oneOf()
    val query = if (kind == 0) T::input(name, T::sort(2), T::sort(1), 128)
      else if (kind == 1) T::input(name, T::sort(2), T::constant(U), 128)
      else if (kind == 2) T::input(name, identityAlias.ty, identityAlias.value, 128)
      else if (kind == 3) T::input(name, T::sort(2), T::sort(0), 128)
      else if (kind == 4) T::input(name, T::sort(2), T::constant(List(122)), 128)
      else if (kind == 5) T::input(name, T::sort(2), T::variable(0), 128)
      else if (kind == 6) T::input(name, T::sort(1), T::letExpr(T::sort(1), T::sort(0), T::variable(0)), 128)
      else if (kind == 7) T::input(name, T::identityType, T::identity, 128)
      else T::input(name, T::sort(1), T::pair(3, T::identity, T::sort(0)), 128)
    perform(query)
  }

  run emptySemanticHistoryTest = init.expect(safety and s.certificates == List())
  run firstPredecessorIsEmptyTest = init.then(perform(typeAlias))
    .expect(safety and s.certificates.nth(0).predecessor == List())
  run compoundCertificateTest = init.then(perform(typeAlias)).then(perform(identityAlias))
    .expect(safety and s.certificates.nth(1).stored.ty == identityAlias.ty
      and s.certificates.nth(1).valueType.value == identityAlias.ty
      and s.certificates.nth(1).normalizedType.value == T::identityType)
  run predecessorMatchesExactPrefixTest = init.then(perform(typeAlias)).then(perform(identityAlias)).then(perform(valueAlias))
    .expect(safety and s.certificates.nth(2).predecessor == previous.checked.environment)
  run threeSuccessfulSemanticRecordsTest = init.then(perform(typeAlias)).then(perform(identityAlias)).then(perform(valueAlias))
    .expect(safety and s.certificates.length() == 3 and s.checked.environment.length() == 3)
  run previousSemanticRecordPreservedTest = init.then(perform(typeAlias)).then(perform(identityAlias))
    .expect(safety and s.certificates.nth(0) == previous.certificates.nth(0))
  run previousLookupPreservedTest = init.then(perform(typeAlias)).then(perform(identityAlias)).then(perform(valueAlias))
    .expect(safety and T::lookup(s.checked.environment, U) == T::lookup(previous.checked.environment, U))
  run semanticWeakeningObservedTest = init.then(perform(typeAlias)).then(perform(identityAlias)).then(perform(valueAlias))
    .expect(safety and s.certificates.indices().forall(i => remainsValidIn(s.certificates.nth(i), s.checked.environment)))
  run projectedPayloadsExactTest = init.then(perform(typeAlias)).then(perform(identityAlias))
    .expect(safety and project(s.checked.environment.nth(1)).ty == identityAlias.ty
      and project(s.checked.environment.nth(1)).value == identityAlias.value
      and project(s.checked.environment.nth(1)).inferred == T::identityType)
  run projectedLookupExactTest = init.then(perform(typeAlias)).then(perform(identityAlias)).then(perform(valueAlias))
    .expect(safety and B::lookup(projectEnvironment(s.checked.environment), nameKey(identityName))
      == List(project(s.checked.environment.nth(1))))
  run projectedUnknownLookupTest = init.then(perform(typeAlias))
    .expect(safety and B::lookup(projectEnvironment(s.checked.environment), nameKey(List(122))) == List())
  run projectedNameLengthDistinctTest = init.expect(safety and nameKey(List(65)) != nameKey(List(65, 65)))
  run mismatchPreservesSemanticHistoryTest = init.then(perform(typeAlias))
    .then(perform(T::input(aliasName, T::sort(2), T::sort(0), 128)))
    .expect(safety and s.certificates == previous.certificates and s.checked.snapshots.nth(1).code == 6)
  run unknownPreservesSemanticHistoryTest = init.then(perform(typeAlias))
    .then(perform(T::input(aliasName, T::sort(2), T::constant(List(122)), 128)))
    .expect(safety and s.certificates == previous.certificates and s.checked.snapshots.nth(1).code == 2)
  run duplicatePreservesSemanticHistoryTest = init.then(perform(typeAlias)).then(perform(typeAlias))
    .expect(safety and s.certificates == previous.certificates and s.checked.snapshots.nth(1).code == 3)
  run duplicateBeforeScopeAndBudgetTest = init.then(perform(typeAlias))
    .then(perform(T::input(U, T::constant(List(122)), T::variable(0), 0)))
    .expect(safety and not(s.checked.halted) and s.checked.snapshots.nth(1).code == 3)
  run rejectedNameCanBeRetriedTest = init.then(perform(T::input(U, T::sort(2), T::sort(0), 128)))
    .then(perform(typeAlias)).then(perform(identityAlias))
    .expect(safety and s.certificates.length() == 2 and s.certificates.nth(0).predecessor == List())
  run forwardReferenceCannotCertifyTest = init.then(perform(valueAlias)).then(perform(typeAlias)).then(perform(valueAlias))
    .expect(safety and s.checked.snapshots.nth(0).code == 2 and s.certificates.length() == 2
      and s.certificates.nth(1).predecessor == List(s.certificates.nth(0).stored))
  run selfReferenceCannotCertifyTest = init.then(perform(T::input(U, T::sort(2), T::constant(U), 128)))
    .expect(safety and s.checked.snapshots.nth(0).code == 2 and s.certificates == List())
  run fatalScopePreservesHistoryTest = init.then(perform(typeAlias))
    .then(perform(T::input(aliasName, T::sort(2), T::variable(0), 128)))
    .expect(safety and s.checked.halted and s.certificates == previous.certificates)
  run fatalBudgetPreservesHistoryTest = init.then(perform(typeAlias))
    .then(perform(T::input(aliasName, T::sort(1), T::sort(0), 0)))
    .expect(safety and s.checked.halted and s.checked.snapshots.nth(1).code == 9 and s.certificates == previous.certificates)
  run haltedSuffixHasNoCertificateTest = init.then(perform(typeAlias))
    .then(perform(T::input(aliasName, T::sort(2), T::variable(0), 128))).then(perform(identityAlias))
    .expect(safety and s == previous and s.certificates.length() == 1)
  run betaValueCertificateTest = init.then(perform(T::input(U, T::sort(1), T::pair(3, T::identity, T::sort(0)), 128)))
    .expect(safety and s.certificates.nth(0).stored.value == T::pair(3, T::identity, T::sort(0)))
  run zetaValueCertificateTest = init.then(perform(T::input(U, T::sort(1), T::letExpr(T::sort(1), T::sort(0), T::variable(0)), 128)))
    .expect(safety and s.certificates.nth(0).stored.value.nth(0) == 6)

  // Begin with two genuinely certified bindings. A legitimate third insertion
  // succeeds, but the unsafe transition also changes the FIRST stored value
  // from Sort 1 to Sort 0. Frozen predecessor evidence is not rewritten.
  pure val negativeBase = replay(List(typeAlias, identityAlias))
  action negativeInit = all { s' = negativeBase, previous' = negativeBase, last' = typeAlias, hasStep' = false }
  action unsafeStep = {
    val valid = advance(negativeBase, valueAlias)
    val wrongOld = { ...valid.checked.environment.nth(0), value: T::sort(0) }
    val wrongEnvironment = List(wrongOld).concat(valid.checked.environment.tail())
    val snapshots = valid.checked.snapshots.slice(0, valid.checked.snapshots.length() - 1)
      .append({ ...valid.checked.snapshots.nth(valid.checked.snapshots.length() - 1), bindings: wrongEnvironment })
    val corrupted = { ...valid, checked: { ...valid.checked, environment: wrongEnvironment, snapshots: snapshots } }
    all { s' = corrupted, previous' = negativeBase, last' = valueAlias, hasStep' = true }
  }

  run forgedDeltaValueProducesOpenFieldTest = init.expect({
    val name = List(65)
    val domain = T::constant(name)
    val ty = T::pair(5, domain, domain)
    val value = T::pair(4, domain, T::variable(0))
    val env = List({ name: name, ty: T::sort(1), value: T::variable(0), inferred: T::sort(1) })
    val result = T::check(env, identityName, ty, value, 16)
    val stored = { name: identityName, ty: ty, value: value, inferred: result.value }
    all {
      T::closed(ty), T::closed(value), T::known(env, ty), T::known(env, value),
      result == { code: 0, value: T::pair(5, T::variable(0), T::variable(0)) },
      not(T::closed(result.value)), not(certificateValid(certificate(env, stored, 16))),
    }
  })

  run closedDeltaSeparatesStoredFromRawInferenceTest = init.expect({
    val name = List(65)
    val ty = T::letExpr(T::sort(2), T::variable(0), T::sort(1))
    val env = List({ name: name, ty: ty, value: T::sort(0), inferred: T::variable(0) })
    val value = T::constant(name)
    val raw = T::eval(env, 2, value, List(), List(), 16)
    all {
      raw == { code: 0, value: ty }, not(T::closed(raw.value)),
      T::check(env, List(66), T::sort(1), value, 16) == { code: 0, value: T::sort(1) },
    }
  })

  run dependentBinderOuterTailScopeTest = init.expect(all {
    T::eval(List(), 3, T::variable(0), List(), List(T::sort(1)), 16) == { code: 0, value: T::sort(1) },
    T::eval(List(), 2, T::variable(0), List(), List(T::variable(0), T::sort(1)), 16)
      == { code: 0, value: T::variable(1) },
    T::closed(T::pair(5, T::sort(1), T::variable(0))),
  })

  run malformedBinderCannotBeItsOwnTypeContextTest = init.expect(all {
    not(T::closed(T::variable(0))),
    T::eval(List(), 2, T::variable(0), List(), List(T::variable(0)), 16)
      == { code: 0, value: T::variable(1) },
    not(T::closed(T::pair(5, T::sort(1), T::variable(1)))),
  })

  run scopedContextWithoutSortTest = init.expect({
    val lambda = T::pair(4, T::sort(1), T::variable(0))
    all { T::closed(lambda), T::eval(List(), 3, lambda, List(), List(), 16).code == 4 }
  })

  run conversionRefusalKeepsInferredFieldAndNameFreeTest =
    init.then(perform(typeAlias)).then(perform(identityAlias))
      .then(perform(T::input(aliasName, T::pair(5, T::sort(1), T::sort(2)), T::constant(identityName), 128)))
      .expect(safety and s.checked.snapshots.nth(2).code == 6
        and T::lookup(s.checked.environment, aliasName).length() == 0
        and s.checked.environment.nth(1).inferred == T::pair(5, T::sort(1), T::sort(1)))
      .then(perform(T::input(aliasName, identityAlias.ty, T::constant(identityName), 128)))
      .expect(safety and s.checked.snapshots.nth(3).code == 0
        and s.checked.environment.nth(2).inferred == s.checked.environment.nth(1).inferred)

  run dependentNormalizationScopeOnExtensionTest = init.expect({
    val name = List(80)
    val p = T::input(name, T::sort(1), T::sort(0), 128)
    val ty = T::pair(5, T::sort(1), T::pair(5, T::sort(1), T::pair(5, T::variable(1), T::variable(2))))
    val value = T::pair(4, T::sort(1), T::pair(4, T::sort(1), T::pair(4, T::variable(1), T::variable(0))))
    val dependent = T::input(identityName, ty, value, 128)
    val specialized = T::input(aliasName,
      T::pair(5, T::sort(1), T::pair(5, T::constant(name), T::constant(name))),
      T::pair(3, T::constant(identityName), T::constant(name)), 128)
    val trace = replay(List(p, dependent, specialized))
    all {
      semanticHistorySafety(trace), trace.checked.environment.length() == 3,
      trace.checked.environment.nth(1).inferred == ty,
      trace.checked.environment.nth(2).inferred == T::pair(5, T::sort(1), T::pair(5, T::sort(0), T::sort(0))),
    }
  })
}

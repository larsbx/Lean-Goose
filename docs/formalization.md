# Definition transactions and stored-binding formalization

Lean-Goose requires two related formal scopes: ordered definition transactions
and preservation of complete stored bindings. Both execute Lean proofs, Quint
checks, and finite comparisons with the bounded Goose reference. The
stored-binding scope adds declared-type, original-value, and inferred-type
payloads plus snapshots after each processed definition.

| Required scope | Lean theorem inventory | Quint deterministic tests | Exhaustive finite action profile |
| --- | --- | --- | --- |
| Ordered names | 21 | 12 | 1,110 nonempty traces over 10 actions, lengths 1–3 |
| Stored bindings | 29 | 16 | 2,954 nonempty traces over 14 actions, lengths 1–3 |

The inventories describe what the gate must execute. They are not a claim that
any particular source revision's acceptance run has passed. The matching formal
and repository receipts record actual execution outcomes and source identities.
Hosted-CI results are assessed separately for the same revision. Each Quint scope also requires 1,000 seeded
simulated traces of at most 40 transitions and a designated invariant-failure
control.

## Ordered-name model and implementation mapping

The model state contains an ordered list of defined names, ordered observations,
a halted flag, and an acceptance-authority flag. The initial lists are empty and
both flags are false. Names are natural numbers in Lean. A completed model receipt
contains the ordered observations, the environment length as its success count,
and the authority flag. A halted state has no completed definition receipt.

The environment is a **projection to names**. It omits the Goose binding's stored
type, value, and inferred-expression fields. Expression checking, normalization,
substitution, caches, and finite resource consumption are abstracted into four
action classes:

| Kind | Concrete DAG specimen | Result for a fresh destination name |
| --- | --- | --- |
| `0`: good definition | `Sort 0` with declared type `Sort 1` | Append name; emit success code `0` |
| `1`: mismatch | `Sort 1` with declared type `Sort 1` | Preserve environment; emit mismatch code `6` |
| `2`: alias | Constant referring to target, with declared type `Sort 1` | Append and emit `0` if target exists; otherwise preserve environment and emit unknown-constant code `2` |
| `3`: scope failure | Free variable `Var 0`, with declared type `Sort 1` | Halt; emit no completed definition-observation object |

An already defined destination name takes priority over every action kind. It
preserves the environment and emits duplicate code `3`, including for an action
whose expression would otherwise fail scope checking. A halted state absorbs
all later actions.

| Implementation surface | Corresponding responsibility |
| --- | --- |
| `reference/checker.goose`: `check_definition` | Duplicate priority, validation before insertion, and environment append on success |
| `reference/checker.goose`: `check_only` | Ordered observation loop, refusal count guard, fatal scope handling, and output fields |
| `tools/run.py`: `definition_observation` | Strict schema, category, order, success-count, and authority validation |
| `tools/runtime.py` | Pinned source verification, derivative verification, compiler invocation, and generated artifact identities |
| `tools/check_formal.py` | Execute the declared proof/model inventory and compare finite model traces with native observations |
| `tools/acceptance.py` | Required-gate orchestration and source-bound repository verification receipt |

The native source checks the duplicate name before examining free variables.
The finite profile uses two names and short, shallow expressions, so duplicate
lookup itself does not exhaust fuel. The abstract model does not claim that this
priority holds independently of all resource failures in arbitrary runtime states.

## Ordered-name Lean statements

The model is in
[`formal/lean/DefinitionTransactions.lean`](../formal/lean/DefinitionTransactions.lean),
namespace `GooseTransactions`. Its statements quantify over arbitrary natural-number
names and arbitrary finite action lists. Principal obligations include:

| Statement | Claim |
| --- | --- |
| `run_environment_exact` | The final name environment equals the names of successful observations, in order |
| `run_environment_unique` | A run from the initial state contains no duplicate environment names |
| `run_success_count_exact` | Environment length equals the number of successful observations |
| `duplicate_precedes_checks` | Duplicate detection precedes the remaining action checks |
| `duplicate_preserves_environment` | A duplicate leaves the name environment unchanged |
| `mismatch_preserves_environment` | A mismatch leaves the name environment unchanged |
| `missing_alias_preserves_environment` | An alias to a missing name leaves the environment unchanged |
| `fresh_good_appends` | A fresh successful definition appends exactly its destination name |
| `mismatch_then_retry_succeeds` | A refused mismatch leaves a fresh name available for a successful retry |
| `halted_run_identity` | Subsequent actions leave an already halted state unchanged |
| `halted_no_receipt` | A halted model state yields no completed definition receipt |
| `run_environment_extends` | Running further actions preserves the existing environment as a prefix |
| `run_preserves_authority` | Transactions preserve the initial authority flag |
| `completed_receipt_has_no_authority` | A completed receipt from the initial state has no acceptance authority |

The step and run preservation lemmas establish the invariants by induction;
these are unbounded statements about the model's finite traces. The gate compiles
the local source in a fresh build, audits all required theorem dependencies, and
checks the local namespace for unexpected axioms. The declared obligations must
remain free of admitted proofs and application-supplied axioms. Any permitted
Lean-generated support axiom is recorded separately from the required obligations.

The executable Lean replay evaluates this same model for the finite comparison
inventory. Its serialization is an observation of model evaluation; a JSON line
for a halted model state is not a native completed definition receipt.

## Ordered-name Quint checks and exploration limits

The executable model is
[`formal/quint/DefinitionTransactions.qnt`](../formal/quint/DefinitionTransactions.qnt).
Its `safety` invariant combines:

- `stateSafety`: ordered environment names equal successful observation names,
  environment names are distinct, outcome codes are recognized, and authority is
  false;
- `refusalAtomicity`: a refusal preserves the preceding name environment; and
- `haltedAbsorbing`: an already halted state remains unchanged.

Twelve deterministic tests exercise concrete obligations:

| Test | Scenario |
| --- | --- |
| `initialStateTest` | Empty initial state and absent authority |
| `successfulDefinitionTest` | Fresh success inserts one name |
| `failedInsertionRetryTest` | Mismatch followed by successful retry of the same name |
| `duplicatePreservesEnvironmentTest` | Duplicate refusal preserves a populated environment |
| `duplicatePreemptsScopeTest` | An existing destination name produces duplicate refusal before scope failure |
| `unknownAliasRecoveryTest` | Missing target, later target insertion, then successful alias retry |
| `validAliasTest` | Alias to an existing definition succeeds |
| `unknownAliasPreservesExistingTest` | Failed alias preserves unrelated existing names |
| `scopeFailureSuppressesReceiptTest` | Scope failure prevents a completed definition receipt |
| `haltAbsorbingTest` | Later actions cannot continue a halted transaction sequence |
| `orderedSuccessCountTest` | Refusal and success retain their order and correct count |
| `authorityPreservedTest` | Completed transactions retain absent authority |

The gate additionally simulates **1,000 traces of at most 40 transitions**, with
seed `20261120`, the TypeScript backend, names `0` and `1`, and the ten-action
inventory below. Successful simulation reports no violation among those sampled
traces. It is neither exhaustive exploration of all forty-step traces nor an
unbounded Quint theorem.

The designated negative control `unsafeStep` incorrectly inserts name `0` while
emitting mismatch code `6`. Its one-step run must find an invariant violation and
emit the two-state ITF witness: the initial empty environment followed by an
inserted name with no successful observation. A parser error, missing executable,
or unrelated nonzero exit cannot satisfy this control.

## Ordered-name finite model and runtime correspondence

The native comparison inventory uses two destination names. There are two good
definitions, two mismatches, four directed aliases, and two scope failures:
**ten actions**. The gate enumerates every nonempty word of length one, two, or
three over that alphabet: **10 + 100 + 1,000 = 1,110 cases**. Each case starts from
a fresh environment.

Lean replay and Quint replay evaluate the same input words. Quint's
[`replay.py`](../formal/quint/replay.py) submits expressions to the pinned Quint
TypeScript evaluator and translates its numeric wire output; it does not
implement a replacement transaction evaluator in Python. Comparing the two
model results covers halted status, ordered observations, ordered name environment,
success count, and authority for this finite inventory.

For the actual Goose executable, comparison uses the strict output schema from
[`schemas/definition-observations-v1.md`](../schemas/definition-observations-v1.md):

- A nonfatal case must produce the expected ordered names and outcome categories,
  the matching success count, and `acceptance_authority: false`.
- A fatal case must exit with code `2` and the designated `Invalid_scope`
  diagnostic, without a completed definition-observation JSON object.

The original `--check` interface does not expose its environment directly. In
this retained lane, alias and retry cases probe its consequences, and a fatal
process emits no partial observation inventory. Its retained model prefix is
therefore compared between the models only. The additional stored-binding lane
below uses the opt-in `--trace` interface to inspect actual binding records and
processed snapshots. Both comparisons remain finite evidence; neither proves a
general refinement theorem for Goose or a translation theorem between Lean and
Quint.

## Stored-binding model and implementation mapping

The additional model is
[`formal/lean/StoredBindings.lean`](../formal/lean/StoredBindings.lean), namespace
`GooseStoredBindings`, and the independently written executable counterpart is
[`formal/quint/StoredBindings.qnt`](../formal/quint/StoredBindings.qnt).

A binding contains `name`, `type`, `value`, and `inferred`. The last three fields
are expression vectors. The model's preservation statements can retain arbitrary
existing vectors; they do not infer or validate arbitrary expressions. The
concrete action constructors use `Sort(level) = [0, level]` and
`Const(name) = [2, name]`. Quint's internal record calls the type field `ty`
because `type` is reserved; its replay exports the common JSON key `type`.

The state contains the full ordered binding environment, semantic observations,
halted and authority flags, and processed snapshots. Actions add a `level` field
to the original kind/name/target vocabulary:

| Action | Behavior for a fresh destination |
| --- | --- |
| Good definition | Append the name with declared type and inferred type `[0, level + 1]`, original value `[0, level]`, and success code `0` |
| Mismatch | Emit code `6`; preserve every existing record |
| Alias | Look up the most recent target; emit `2` if absent, emit `6` if its stored type differs from `[0, level + 1]`, otherwise append the exact desired type, original value `[2, target]`, target type as the inferred field, and code `0` |
| Scope failure | Preserve every existing record and halt without a semantic outcome |

Duplicate destination names still emit code `3` before all other action checks,
including type-level disagreement and scope failure. Each processed action
appends a snapshot `{name, code, environment}` containing the environment after
that step. Fresh scope failure records snapshot code `1` but adds no semantic
outcome. An already halted state adds neither outcomes nor snapshots.

Most-recent lookup is defined for arbitrary model environments, including
hypothetical environments with duplicate names. Reachable environments from the
initial state satisfy uniqueness; the lookup definition does not hide that
assumption inside a first-match shortcut.

| Implementation surface | Stored-binding responsibility |
| --- | --- |
| `reference/checker.goose`: `check_definition` | Original checking and insertion into full binding records |
| Opt-in native `--trace` interface | Immediate snapshots of raw records and immutable node payloads after each processed definition |
| `tools/stored_binding_profile.py` | Bounded inputs, strict trace decoding, raw-record preservation checks, and native/model projections |
| `tools/check_stored_bindings.py` | Execute the new proof/model inventories and both native modes for every case |
| `tools/binding_trace_controls.py` | Required diagnostic contract and envelope controls |
| `tools/source_derivation.py` | Reconstruct the exact reviewed diagnostic extension and verify the preserved checking/parser prefix |
| `tools/check_formal.py` | Require both formal scopes in one source-bound receipt |

### Stored-binding Lean obligations

The stored-binding audit inventory contains **29 named, axiom-free required
theorems**. The scoped audit covers **196 declarations and 63 theorem
declarations** in `GooseStoredBindings`; only generated support uses `propext`.
Every required theorem's transitive axiom set is empty. The final gate must
replay this audit for the source under review; the scoped audit result alone
does not establish complete repository acceptance.

Principal statements include:

| Statement | Claim, under its stated hypotheses |
| --- | --- |
| `lookup_latest_binding` | Appending a binding makes it the most recent match for its name |
| `lookup_append_fresh_preserves_existing` | A fresh append preserves lookup of an existing name |
| `fresh_good_payload_exact` | Successful good insertion records exactly the declared type, original value, and inferred type vectors |
| `fresh_alias_payload_exact` | A type-matching alias records its original constant value and the target's exact stored type |
| `duplicate_precedes_checks` | Duplicate detection retains priority over the other checks |
| `duplicate_preserves_environment` | Duplicate refusal preserves the complete binding environment |
| `mismatch_preserves_environment` | Mismatch refusal preserves the complete binding environment |
| `missing_alias_preserves_environment` | Missing-target refusal preserves the complete binding environment |
| `wrong_type_alias_preserves_environment` | Alias type disagreement preserves the complete binding environment |
| `run_environment_extends` | The original full-record environment remains a prefix after a finite run |
| `run_preserves_existing_binding` | Every previously indexed binding remains exactly the same record |
| `run_preserves_existing_binding_fields` | Previously stored name, type, value, and inferred fields remain equal |
| `run_preserves_existing_lookup` | Lookup of an existing name retains its original binding |
| `run_preserves_name_uniqueness` | A run preserves the initial environment's name uniqueness |
| `run_success_names_exact` / `run_success_count_exact` | Runs from the initial state relate successful observations to environment names and length |
| `halted_run_identity` / `halted_no_receipt` | Later actions preserve a halted state, which has no completed receipt |
| `run_preserves_authority` / `completed_receipt_has_no_authority` | Transactions preserve authority, and initial-state receipts have none |

The complete required names are in
[`StoredBindingsAudit.lean`](../formal/lean/StoredBindingsAudit.lean) and the estate
manifest. These are unbounded model statements about finite action lists and
arbitrary natural-number names and levels. Full-record preservation retains
opaque payloads; it does not prove that arbitrary payloads have valid Lean types.
Snapshots are evaluated by the same executable model and compared in the finite
profile; a general native snapshot/refinement theorem remains open.

### Stored-binding Quint checks

The stored model's `safety` invariant combines full-record state and snapshot
consistency, `refusalAtomicity`, `oldBindingsPreserved`, and `haltedAbsorbing`.
In particular, existing records must remain equal as a prefix, including all
payload elements. Every recorded snapshot's environment must agree with the
subsequent preserved records, and the final snapshot must match the current
environment.

Sixteen deterministic tests are required:

| Test | Scenario |
| --- | --- |
| `initialStoredStateTest` | Empty initial bindings, outcomes, and snapshots |
| `goodPayloadLevelZeroTest` | Exact payload for the level-zero good definition |
| `goodPayloadLevelOneTest` | Exact payload for the level-one good definition |
| `typedAliasPayloadTest` | Alias retains its constant value and exact stored type |
| `wrongTypeAliasRefusalTest` | Existing target with a different type causes refusal |
| `duplicatePreservesAllFieldsTest` | Cross-level duplicate cannot replace any existing field |
| `crossLevelDuplicateAliasTest` | Duplicate priority precedes missing-target/type disagreement |
| `mismatchPreservesAllFieldsTest` | Mismatch preserves an existing higher-level binding |
| `unknownAliasPreservesAllFieldsTest` | Missing target preserves unrelated full records |
| `refusalThenRetryTest` | Wrong-type alias refusal followed by a correctly typed retry |
| `levelOneAliasTest` | Successful level-one alias payload |
| `scopeSnapshotTest` | Final scope snapshot with no corresponding semantic outcome |
| `duplicatePreemptsScopeSnapshotTest` | Duplicate priority produces a nonfatal snapshot |
| `haltStopsSnapshotsTest` | Later input cannot add snapshots after a fatal step |
| `orderedSnapshotCountTest` | Refusal and successful extensions preserve snapshot order |
| `storedAuthorityPreservedTest` | Stored-binding observations retain absent authority |

The manifest identifies the new obligations as `StoredBindings.safety` and
`StoredBindings.<test>`, keeping them distinct from the retained transaction
model's obligation names. The gate simulates **1,000 traces of at most 40
transitions** using seed `20261120`, the TypeScript backend, and the fourteen-action
profile below. This is sampled bounded exploration; the exhaustive short profile
is a separate check.

The payload-corruption control uses `unsafeInit`, a reachable state after a good
level-zero definition for name `0`, followed by `unsafeStep`. The unsafe step
refuses fresh name `1` with mismatch code `6` but changes binding `0`'s original
value from `[0, 0]` to `[0, 999]`. Its name, declared type, and inferred type
remain unchanged. The final refusal snapshot records the corruption while the
previous snapshot retains the original record.

The negative run must use `--init=unsafeInit --step=unsafeStep`, return the
designated invariant failure, and preserve its two-state ITF witness. Both
states retain false authority. Parser/type errors, arbitrary process failure,
or a counterexample about a different action do not satisfy this control.

## Stored-binding finite native correspondence

The alphabet consists of the original ten level-zero actions, two level-one
good definitions, and two cross-name level-one aliases: **14 actions** over names
`0` and `1`. The gate enumerates every nonempty word of lengths one through three:
**14 + 196 + 2,744 = 2,954 cases**. Each starts from an empty environment.
The required inventory partitions into **2,032 completed cases**, **922 scope
terminations**, and **7,546 processed snapshots**. These are acceptance inventory
counts, not a declaration that a particular revision's native run has passed.

[`StoredBindingsReplay.lean`](../formal/lean/StoredBindingsReplay.lean) and
[`stored_replay.py`](../formal/quint/stored_replay.py) evaluate the same four-field
input words. The latter invokes actual Quint `replayProfile` evaluation and only
decodes numeric wire framing. It checks exact coverage and uniqueness of all
2,954 trace identities before returning requested results. The models are
compared on the complete environment, all payload vectors, ordered outcomes,
halted status, success count, authority, and every processed snapshot.

For **each case**, the gate checks both actual native modes:

- `--trace` must report the expected processed prefix, outcomes, stored records,
  decoded Sort/Const type/value/inferred payloads, success count, authority,
  status, and designated fatal diagnostic when applicable. Existing raw binding
  IDs and immutable node payloads must be preserved across snapshots.
- `--check` must retain the original strict observation contract. Completed
  cases produce matching ordered observations and counts. Scope-terminated
  cases return exit `2` with the `Invalid_scope` diagnostic and no completed
  JSON receipt.

The [diagnostic trace schema](../schemas/binding-trace-v1.md) carries raw node IDs
and each snapshot's immutable node DAG. The renderer serializes stored fields
after checking, without re-running inference or reconstructing a value from its
target. The adapter can therefore distinguish an alias's original constant
expression from the target's value, and inspect earlier successful bindings even
when a later scope failure terminates the run.

The trace schema supports the reference's node tags more broadly, but this
formal correspondence profile decodes **Sort/Const payloads** only. The model's
unbounded preservation of arbitrary records and the native finite comparison
have different scopes. Neither establishes general expression refinement,
cache/context/fuel correspondence, or correctness of all diagnostic serialization.

### Source derivation and retained gates

The `lean-goose.source-provenance.v2` contract reconstructs the local reference
from the immutable upstream file, applies the original four presentation
replacements, then applies the reviewed diagnostic patch exactly. It binds the
patch and final-source hashes and preserves the **18,034-byte checking/parser
function prefix of the presentation-adapted base**. Patch application does not permit fuzzy
context or an alternate source path. The opt-in trace dispatch and renderer are
local, reviewable additions; the original algorithmic functions retain their
verified source relationship.

The original transaction lane remains required. The broader comparison still
checks **964 ordered outcomes per engine across 16 fixtures**, with **six
parser/scope/resource controls**. The benchmark smoke continues to run all seven
families using eight definitions, one sample, and one worker per engine. These
checks retain their finite testing purposes and do not become full mathematical
refinement or new performance measurements through this increment.

## Reproduction and receipts

Use the pinned Lean `4.34.1` toolchain at revision
`5045d0056413266e57c625dcd7c365b10e377c52`, Quint `0.33.1`, and the pinned Goose
compiler. The workflow uses Node `24.22.3`. With the external compiler and
comparison paths configured as in the [README](../README.md):

```sh
npm --prefix formal/quint ci --ignore-scripts --no-audit --no-fund
make formal-tests
make formal
make acceptance
```

`LEAN` can name the pinned executable; `QUINT` can name the pinned CLI. The default
Quint installation is under `formal/quint/node_modules`. Tool reports and hashes
belong to the actual run. Formal Lean commands use the recorded `--threads=1`
flag for a fixed worker count, without changing the proof or axiom checks. The formal receipt is
`conformance/evidence/formal/results.json`, schema `lean-goose.formal-evidence.v2`,
with a required `stored_bindings` section in addition to the retained scope.
The repository receipt is `conformance/evidence/verification.json`.

The gate requires both formal scopes, their Lean and Quint lanes, actual finite
runtime comparisons, and unchanged source identities. Declared scope, implementation, model, gate, and profile files
must occur in its source inventory. Logs and receipt outcomes are generated by
execution. CI retains its own evidence, and local success is recorded separately
from hosted status at a particular revision.

Full stored-binding replay and native-comparison logs are gzip-compressed:

- `stored-lean-replay.log.gz` and `stored-quint-replay.log.gz` retain the complete
  model replay outputs.
- `stored-native-comparison.jsonl.gz` retains the model and actual native stdout
  and stderr for each case.
- `stored-binding-inputs.txt` records the exact input words.

These files are under `conformance/evidence/formal/`; the receipt identifies
content digests. Read a compressed log with `gzip.open`:

```sh
python3 - conformance/evidence/formal/stored-native-comparison.jsonl.gz <<'PY'
import gzip
import sys
with gzip.open(sys.argv[1], "rt", encoding="utf-8") as stream:
    for line in stream:
        sys.stdout.write(line)
PY
```

A halted diagnostic projection in those logs is evidence of the processed prefix,
not a completed definition receipt. A local passed receipt and a hosted job
conclusion remain separate facts.

## Remaining assumptions and obligations

The semantic action classification is an abstraction. The general correctness
of Goose's inference, substitution, conversion, caching, parser, and compiler is
not established by this model. Resource exhaustion, height limits, arbitrary
expression graphs, and the semantic refusals `Expected_sort` and
`Expected_function` lie outside this four-action formal scope. Existing expression,
parser, and resource controls remain part of `make acceptance` and retain their
finite-test meaning.

The stored-binding model establishes full-record preservation at its abstract
boundary; native correspondence currently covers the declared finite Sort/Const
profile. The next obligations are structural expression/DAG correspondence,
capture-avoiding substitution and scope preservation, typing/conversion rules,
and refinement of actual runtime transitions. Runtime/tool authenticity,
faithful diagnostic serialization, filesystem consistency, and source-hash
assumptions remain in the execution boundary. Concrete work is listed in
[roadmap.md](roadmap.md).

This formalization grants no declaration, theorem, operational, or deployment
admission authority and makes no estate-wide coverage claim. It also makes no
new performance claim; historical benchmarks retain their original source
identity until a fresh full measurement is explicitly run.

# Ordered definition transaction formalization

This repository's initial estate-v3 scope is the ordered transaction behavior of
its bounded Goose reference. The model captures when a definition changes the
environment, how semantic refusals affect subsequent definitions, and when the
process terminates without a completed observation object. Both Lean and Quint
are required execution lanes for this scope.

## Model and implementation mapping

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

## Lean statements

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

## Quint checks and exploration limits

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

## Finite model and runtime correspondence

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

Goose does not expose its name environment directly. Alias and retry cases probe
its consequences, but the runtime comparison does not inspect its full internal
state. A fatal process emits no partial observation inventory, so its retained
model prefix is compared between the models only. These are finite correspondence
observations; they do not prove a general refinement theorem for Goose or a
translation theorem between Lean and Quint.

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
belong to the actual run. The formal receipt is
`conformance/evidence/formal/results.json`; the repository receipt is
`conformance/evidence/verification.json`.

The gate requires both lanes, actual finite runtime comparison, and unchanged
source identities. Declared scope, implementation, model, gate, and profile files
must occur in its source inventory. Logs and receipt outcomes are generated by
execution. CI retains its own evidence, and local success is recorded separately
from hosted status at a particular revision.

## Remaining assumptions and obligations

The semantic action classification is an abstraction. The general correctness
of Goose's inference, substitution, conversion, caching, parser, and compiler is
not established by this model. Resource exhaustion, height limits, arbitrary
expression graphs, and the semantic refusals `Expected_sort` and
`Expected_function` lie outside this four-action formal scope. Existing expression,
parser, and resource controls remain part of `make acceptance` and retain their
finite-test meaning.

The model records names rather than typed bindings; preservation of stored type,
value, and inferred-expression fields requires further correspondence work.
Runtime/tool authenticity, faithful serialization, filesystem consistency, and
source-hash assumptions remain in the execution boundary. The concrete next
obligations are listed in [roadmap.md](roadmap.md).

This formalization grants no declaration, theorem, operational, or deployment
admission authority and makes no estate-wide coverage claim. It also makes no
new performance claim; historical benchmarks retain their original source
identity until a fresh full measurement is explicitly run.

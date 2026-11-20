# Expression/DAG representation and binder scope

This formal scope connects the immutable raw DAG exposed by native `--trace`
to structural expressions and explicit binder-depth requirements. It covers all
seven constructors: Sort, variable, constant, application, lambda, Pi, and let.
The existing ordered-name and stored-binding scopes remain required. This
increment grants no theorem or definition admission authority.

The exact input, output, token grammar, and refusal behavior are defined in the
[expression-DAG replay contract](../schemas/expression-dag-replay-v1.md). The
[native trace contract](../schemas/binding-trace-v1.md) remains unchanged; this
scope adds model evaluation and finite comparisons over its existing data.

## What is represented

A raw node's list position is its ID. Leaves carry a sort level, de Bruijn index,
or constant-name byte vector. Compound nodes carry IDs of earlier nodes. The
decoder processes the table in order and constructs a structural expression for
each node from its already decoded children. Self references, forward references,
escaping IDs, and cycles cannot decode successfully.

The structural prefix wire retains every constructor and payload. Constant
names retain their actual ASCII bytes, with an explicit length; there is no
renaming or symbol-table equivalence assumption. Shared nodes remain identified
in the raw request, while the structural wire expands their contents at each
use. Comparing the structural wire therefore complements the raw ID and payload
comparison rather than replacing it.
The expanded structural expression need not preserve physical sharing.

Successful decoding also returns structural height and the minimum number of
ambient binders required to put every variable in scope. A variable of index
`i` needs `i + 1` ambient binders. Application takes the maximum requirement of
its children. Lambda and Pi decrement only the body's requirement, saturating
at zero; let decrements only the body's requirement, leaving its type and value
outside that binder. An expression is in scope at depth `d` exactly when its
requirement is at most `d`.

This distinction matters for sharing. `Var 1` needs two ambient binders. A lambda
whose body is that variable still needs one ambient binder. Putting that lambda
under another binder can close it. The same raw subtree can therefore be open
at one use depth and closed at another; a node-ID-only closedness observation
cannot replace an explicit depth query.

An invalid whole table produces `decoded: false` and four empty semantic
arrays. That topology result is distinct from a malformed request or evaluator
failure, both of which require a nonzero replay-helper exit. A successful empty
table is valid and produces `decoded: true` with empty arrays.

The native parser can import open expressions into a DAG. Closure is enforced
when a fresh definition is checked, after the existing duplicate-name check.
Constants are scope-closed leaves that retain opaque name bytes: `Scoped` does
not resolve an environment or establish constant existence or type correctness.
Native missing-constant controls and the earlier stored-binding preservation
scope therefore remain separate obligations.

## Lean specification and proof boundary

[`ExpressionDag.lean`](../formal/lean/ExpressionDag.lean), in namespace
`GooseExpressionDag`, distinguishes raw nodes, inductively defined structural
expressions, an ordered decoder, an independent representation relation, and an
inductive scope relation. Natural-number fields and opaque constant-name lists
are part of the core model. Canonical ASCII/native-wire restrictions belong to
the adapters.

The 30 required named obligations cover decoding soundness and completeness
against the independent representation relation, successful decoding exactly
for topological inputs, exact decoded-table length, and the absence of nonempty
directed cycles. Further obligations cover preservation of old expressions under
valid table extension, consistent decoding of repeated/shared children, scope
and required-depth equivalence, positive height and strict child-height bounds,
empty projections on refusal, and absent acceptance authority.

These are statements about arbitrary finite model inputs; they are not
restricted to the Quint simulator's arena bound or a finite native fixture
profile. Compilation and the complete namespace audit in
[`ExpressionDagAudit.lean`](../formal/lean/ExpressionDagAudit.lean) must execute
for the exact source under review. Required theorem dependencies must be free
of admitted proofs and application-supplied axioms; any permitted generated
support axiom is reported separately.

[`ExpressionDagReplay.lean`](../formal/lean/ExpressionDagReplay.lean) projects
the same model into the shared JSON contract. Its agreement with another
evaluator on a finite inventory is a separate piece
of evidence from the Lean statements. Required theorem inventories and the
actual audit result belong to the manifest and matching formal receipt; this
document does not assert a completed acceptance run.

## Quint invariants and bounded exploration

[`ExpressionDag.qnt`](../formal/quint/ExpressionDag.qnt) computes structural
wires, heights, and loose-variable requirements bottom-up. It keeps an internal
valid raw/decoded prefix and an explicit decode flag. Its public projection
suppresses all semantic arrays after a topology refusal.

`ExpressionDag.safety` combines:

- `stateSafety`: accepted raw nodes have earlier child IDs, the decoded row at
  every ID has the exact constructor wire and metadata, heights are positive,
  requirements are nonnegative, and authority is false;
- `immutablePrefix`: every later internal state retains the earlier raw and
  decoded records as exact prefixes;
- `refusalAtomicity`: a topology refusal changes no accepted raw or decoded
  prefix and marks decoding unsuccessful; and
- `refusedAbsorbing`: later actions cannot resume a refused decoding run.

The required bounded simulation uses Quint `0.33.1`, its TypeScript backend,
seed `20261120`, **1,000 samples**, and **at most 40 transitions per sample**.
Its arena grows to at most **eight nodes**, then stutters. The empty arena
permits only Sort, variable, and constant leaves; subsequent
steps can select any of the seven tags. Leaf payloads are `0..3`, and every
earlier child ID is available; constant names are the ASCII identifiers `n0`
through `n3`. The explicit
arena cap bounds expansion of highly shared expressions. This is sampled
bounded exploration, not exhaustive enumeration of all forty-step runs or an
unbounded Quint proof. The replay helper does not impose the simulator's
eight-node cap on supplied finite DAGs.

The model has 21 deterministic tests:

| Test | Obligation exercised |
| --- | --- |
| `emptyDagTest` | Valid empty table and absent authority |
| `leafPayloadsTest` | Exact Sort, variable, and constant payloads |
| `applicationDecodeTest` | Application wire, maximum requirement, and height |
| `lambdaBinderTest` | Lambda binds the body's variable |
| `piBinderTest` | Pi binds the codomain's variable |
| `letBinderTest` | Let binds its body |
| `openDomainNotBoundTest` | A binder does not close its own domain |
| `letValueNotBoundTest` | A let does not bind variables in its value |
| `nestedBinderDecrementTest` | Exactly one decrement for each nested binder |
| `sharedOpenSubtreeDepthTest` | One shared subtree at different ambient depths |
| `selfReferenceRefusalTest` | Self references are refused without a partial projection |
| `forwardReferenceRefusalTest` | Later IDs cannot serve as earlier children |
| `escapingReferenceRefusalTest` | Out-of-table child IDs are refused |
| `cyclicReferenceRefusalTest` | A cyclic input cannot begin a decoded table |
| `snapshotPrefixPreservedTest` | Later nodes preserve old raw and decoded records |
| `refusedDagHasNoExpressionsTest` | Whole-table refusal has no semantic arrays |
| `scopeDepthMonotoneTest` | Sufficient ambient depth stays sufficient at larger depths |
| `exactHeightTest` | Nested compound height is the exact maximum plus one |
| `constantNamesLosslessTest` | Distinct name lengths and bytes retain their identity |
| `dagAuthorityPreservedTest` | Decoding grants no acceptance authority |
| `simulationBoundStuttersTest` | The eight-node simulation cap preserves the state |

### Designated bad-binder control

The negative run uses `unsafeInit`, `unsafeStep`, and invariant `safety`. Its
initial state is a reachable two-node table containing `Sort 0` and `Var 1`,
with requirements `[0,2]`. The unsafe step appends a lambda with domain ID `0`
and body ID `1`, but decrements the body's requirement by two instead of one.

The exact bad final row has structural wire `[4,0,0,1,1]`, height `2`, and
incorrect requirement `0`. The correct requirement is `1`. Thus the wrong
metadata would falsely report that this expression is in scope at depth zero.
The earlier raw nodes and decoded rows remain unchanged, and both states keep
`acceptance_authority: false`.

The gate must obtain an actual invariant violation and a two-state ITF witness
matching that transition, including the previous state, action, raw nodes,
wire, height, and incorrect requirement. A missing executable, parse error,
timeout, or unrelated nonzero exit cannot satisfy this control.

## Actual replay and native correspondence

[`dag_replay.py`](../formal/quint/dag_replay.py) invokes the actual pinned Quint
evaluator in one process per helper invocation. It submits commands of at most
32 canonical node/depth requests, checks the full echoed request identities and
ordinals, and translates only numeric result framing into JSON. It does not
calculate expressions, heights, scope, or topology in Python. All internal
batches must validate before that invocation emits any result.

The owned gate divides the complete ordered inventory into sequential Quint
helper invocations of at most 256 requests. A fresh process bounds retained
REPL source/history and memory. Lean evaluates the entire inventory once; each
Quint chunk must match the corresponding Lean slice exactly. The whole input
is retained, and the receipt records every chunk's starting index, case count,
stdin hash, command name, and associated compressed log identity. No case is
removed or sampled by this process grouping.

### Required finite inventory

The generated alphabet has seven leaves: `Sort 0`, `Sort 1`, variables
`Var 0` through `Var 3`, and `Const missing`. At node position `i`, a compound
node can select any earlier ID for each of its children. The three binary
constructors contribute `3 * i²` options, and let contributes `i³` options.

| Node position | Leaf options | Binary options | Let options | Total options |
| --- | --- | --- | --- | --- |
| `0` | `7` | `0` | `0` | `7` |
| `1` | `7` | `3` | `1` | `11` |
| `2` | `7` | `12` | `8` | `27` |

Every graph of length one, two, or three over that bounded inventory is
included: **7 + 7 × 11 + 7 × 11 × 27 = 7 + 77 + 2,079 = 2,163 graphs**.
Each graph's final node is probed at ambient depths `0`, `1`, `2`, and `3`,
giving **8,652 native scope probes**. The model replay also returns the
expressions and metadata of every node in each graph.

The initial model inventory additionally contains **one empty DAG**,
**27 malformed-topology controls**, and **17 named controls**:
**2,163 + 1 + 27 + 17 = 2,208 model cases**. Malformed controls cover self,
forward, and missing references in every meaningful child position of the
binary and let constructors. Named controls exercise shared and dependent
identities, nested binders, application, Pi and let bodies, open domains/types/
values, scope-before-unknown behavior, duplicate-before-scope behavior, and
transparent constant payloads.

The empty DAG is model-only. Each generated depth probe runs native `--trace`.
The **44 malformed and named controls** run both `--trace` and `--check`,
requiring **8,652 + 2 × 44 = 8,740 native process executions**. These are required
inventories, not a claim that the current source has completed its acceptance
run. The set of unique arenas and the number of snapshots actually emitted by
those native executions are measured and recorded in the receipt; they are not
fixed constants in this profile.

### Comparison boundary and evidence

Finite comparison sends the same raw graphs and requested depths to Lean and
Quint and requires exact equality of all six response fields. For native
snapshots, the adapter must retain the existing raw IDs, translate the seven
native tag characters exactly, and preserve constant names byte-for-byte. It
must compare successive raw-node prefixes as well as the decoded projections.
These checks cover the data actually emitted by the native execution, including
derived arena entries present in its diagnostic snapshots.

The native trace omits node `height`, `free`, normalization/inference caches,
context stacks, and fuel counters. Consequently, replayed height and scope are
independent structural calculations over the emitted payloads. They are not
direct observations or general correctness proofs of the native cached
metadata. Any native success, semantic refusal, or fatal-scope comparison is
limited to the registered finite cases and the actual process results saved in
the matching evidence.

Source-bound formal and repository receipts record the exact fixture inventory,
model/native comparisons, theorem audit, deterministic tests, simulation limits,
and designated counterexample. Local results and hosted CI remain distinct.
The required finite counts above define coverage; the matching receipts establish
which executions completed and whether the complete gate passed.

## Remaining obligations

This scope establishes representation and binder-depth requirements within the
declared models. It does not establish substitution or shifting correctness,
capture avoidance, typing, definitional equality, normalization, cache validity,
resource accounting, parser or compiler correctness, or general implementation refinement.
Structural constants are considered in scope independently of environment
lookup; this is not a proof that they are defined or well typed.

The next semantic obligations are expression substitution and binder-sensitive
operations, followed by typing/conversion and a precise refinement relation to
the actual checker. Broader native correspondence needs additional registered
inputs and proof obligations. Any admission boundary still requires an explicit
authority decision; adding this formal scope does not create one.

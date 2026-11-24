# Authority and architecture

Lean-Goose is a candidate research repository for a bounded Goose reference.
It owns no theorem, declaration, operational, or deployment admission boundary.
`[authority].acceptance_authority = false` records that fact. Implementation
languages are unrestricted under estate-repository-v3; the current language
inventory describes the implementation rather than assigning authority.

## Authority and implementation

| Plane | Implemented role |
| --- | --- |
| `policy/` | Governance, evidence, and publication policy |
| `reference/` | Locally owned, bounded Goose checking observations |
| `formal/` | Lean transaction, full-record binding, DAG/scope, substitution, typing/conversion, and semantic-environment proofs with independent Quint checks |
| `oracles/` | Contract for pinned external Lean and OCaml comparisons |
| `schemas/` | Versioned input and observation contracts |
| `conformance/` | Source identities, dependency pins, and generated observations |
| `tools/` | Builds, external source verification, comparison, formal gates, and receipts |
| `tests/` | Formal-runner acceptance and rejection controls |
| `docs/` | Scope, reproduction, historical results, and next obligations |

The repository is one program. It has no authoritative kernel and needs no
placeholder kernel directory. The local reference and models report bounded
observations and scoped mathematical claims under their declared assumptions.

## Owned reference

`reference/checker.goose` is an explicitly adopted derivative of the Goose
prototype in Lean-OCaml at the recorded source commit. Source provenance v2
reconstructs the local file in two stages: the original four presentation changes,
then the exact reviewed `reference/binding-trace.patch`. The verifier requires
exact patch context and offsets, the patch digest, and the final local digest.
It also verifies that the presentation-adapted base's checking and parser
function prefix before `main` remains byte-for-byte unchanged.

The patch adds diagnostic serialization and opt-in `--trace` dispatch. It uses
the existing `check_definition` result and stored records; the renderer performs
no fresh inference, normalization, substitution, or validation. The existing
`--check` and timing contracts remain subject to their full regression gates.
The trace adds its own bounded output envelope without changing the original
checker or parser limits.

The checker observes success or a designated refusal for transparent monomorphic
definitions. Its success label is `observed_success`; its output declares
`acceptance_authority: false`. A test `passed` status means the behavior matches
a registered finite expectation. The local observation protocol confers no
domain admission rights.

## Formal transaction, stored-binding, and expression boundaries

The transaction and stored-binding scopes map to `check_definition` in the Goose reference. The
original ordered-name model captures duplicate priority, successful insertion,
refusal atomicity, success counts, and termination without a completed `--check`
receipt. Its 21 Lean obligations and 1,110-case comparison remain required.

The additional model represents each binding's name, declared type, original
value, and inferred type. Lean's full-record preservation statements quantify
over arbitrary existing payload vectors and finite action traces. They establish
that extension retains the old records and lookups, while refusals retain the
entire environment. The model's successful insertion rules are still an abstract
four-action specification, with exact type equality for the scoped aliases.
They do not implement general expression typing or reduction.

The stored-binding gate requires 29 named Lean obligations, a complete namespace
axiom audit, an independent Quint model, 16 deterministic Quint tests, bounded
simulation, and a deliberate payload-corruption counterexample. It evaluates all
2,954 nonempty action sequences of lengths one through three from the declared
14-action profile. Native comparison covers Sort/Const payloads at levels zero
and one, two names, duplicates, refusals, retries, and scope termination.

The expression-DAG model maps topology-ordered raw nodes to structural
expressions for all seven constructor kinds. Its Lean proofs establish the
decoder's representation relation, topology criterion, acyclicity, length and
prefix preservation, and recursive scope equivalence to the minimum required
binder depth. Shared child IDs are retained in raw traces; structural decoding
expands their meaning and does not claim a unique or physically shared tree
representation. Height is a structural measure in the models.

This third lane requires 30 axiom-free Lean theorems, 21 Quint tests, bounded
simulation with an eight-node cap, and a wrong-binder-decrement counterexample.
The native finite profile probes every one-to-three-node valid DAG over the
selected seven leaves at depths zero through three, plus malformed topology
and named context controls. All observed raw arenas are independently decoded
by both actual models. Full details and the exact limits are in
[docs/expression-dag-scope.md](docs/expression-dag-scope.md).

The fourth lane defines structural lifting and capture-avoiding substitution
over that expression type. Its 32 required Lean theorems include cutoff rules,
scope preservation, lift composition, insertion/removal identities, and
noncapture under arbitrarily many lambda binders. Quint independently computes
the operations, with 30 deterministic tests, a bounded six-node simulation, and
an exact negative witness that captures a free variable by omitting its lift.

The native transformation harness is generated temporarily from the exact
owned checker. It renames the unique main entrypoint and appends the separate
`reference/substitution-driver.goose`; all original algorithm, parser, import,
resource, and serializer functions are preserved byte for byte. The gate
verifies reversible derivation and records checker, driver, generated source,
C, and binary identities. The driver calls the actual functions on open syntax
without performing definition insertion. It exposes a result ID and raw arena,
with `null` result on a fatal operation. It has no admission authority.

The transformation profile compares 2,546 complete Lean/Quint observations with
actual native behavior and requires 30 additional native control commands.
Result structure and original raw IDs are checked; native internal `free` and
height fields remain unobserved. Native parser, import, fuel, index, height, and
trace-envelope refusals are separate from pure mathematical topology refusal.
See [the substitution scope](docs/substitution.md) and its
[replay contract](schemas/substitution-replay-v1.md). This finite comparison is
not a general refinement proof of the concrete functions.

The fifth lane reuses those expressions and transformations to specify the
checker's numeric-sort inference and beta/zeta/delta conversion. Successful
execution of the Lean model derives independent typing and reduction judgments.
The definition-checking bridge connects normalized inferred types to original
declared types and exact stored records. A dedicated model recursion budget is
distinct from native work accounting. The owned checker and earlier four model
sources are unchanged.

The gate adds 32 required axiom-free Lean theorems, 26 deterministic Quint tests,
bounded exploration, and a precise wrong-inferred-field negative witness.
Both actual models replay 48 authored compound cases; native `--trace` and
`--check` execute each case. Forty-four common-fragment fixtures additionally
produce 59 ordered outcomes per external engine in the conformance gate.
Those external drivers observe success/refusal, while the native diagnostic
interface exposes full stored fields. See [typing/conversion](docs/typing-conversion.md).
This proves successful model evaluation satisfies its rules and supplies finite
implementation evidence. Typed reduction preservation, sufficient-budget
completeness and native refinement remain open.

The sixth lane proves semantic-environment preservation for the existing typing
model. Independent predecessor certificates contain closed/available original
syntax and `HasSort`, `Infers`, `Normalizes`, and `Converts` derivations.
Lookup-preserving extension weakens these judgments into the current environment;
all processed snapshots and the final environment preserve certification.
A projection retains complete encoded records and reuses the earlier
stored-binding preservation theorem. Lookup correspondence explicitly assumes
an injective name coding; the older four-action checker is not simulated.

The gate requires 88 Lean theorems, 31 Quint tests, bounded exploration, an
exact old-value corruption witness, and 18 native/model histories. Fifteen
common-reference histories add 69 outcomes per engine. Scope and availability
hold for all stored fields in certified snapshots. The model defines valid
binder contexts and proves structural preservation of inferred types.
Binder insertion preserves exact lifted inference and sort levels. General
typed substitution and subject reduction remain open.
See [semantic environments](docs/semantic-environment.md).

### Observable diagnostic interface

`checker --trace FILE` exposes each processed definition's outcome, complete
stored binding records, and immutable raw node table. A binding's `type`, `value`,
and `inferred` fields retain their actual node IDs. The table provides structural
payloads and child IDs, allowing the adapter to check both raw-record preservation
and decoded payload equality. Snapshots are serialized immediately after the
check, before the next definition can change the state. Trace input, node,
definition, arena, and serialized-output bounds are specified in the
[trace contract](schemas/binding-trace-v1.md).

A fatal checker result produces a final diagnostic snapshot in `--trace`, with
`status: halted` and a nonzero exit. The original `--check` mode still emits no
completed receipt for that fatal run. The formal gate checks both modes for every
stored-binding profile case, including the processed prefix before termination.
The diagnostic data grants no admission authority.

The trace omits mutable node caches, context stacks, fuel, and derived metadata.
The DAG lane verifies structural expression payloads and native scope outcomes
across all node kinds in its finite profile. Native scope is observed through
fresh-definition completion or the designated fatal `Invalid_scope` result;
internal metadata is not directly compared. General correctness of the trace
adapter and refinement of arbitrary runtime behavior by the models remain open.
The complete claims, required inventories, and limits
are in [docs/formalization.md](docs/formalization.md); execution outcomes belong
to the receipt for the exact source tested.

## External comparison boundary

Goose, Lean, and OCaml receive identical generated DAG inputs. The native Lean
process performs checked declaration insertion at trust level zero. That process's
checking boundary stays with Lean. The adapter translates its success observation
to this repository's vocabulary before saving local evidence.

The two explicitly registered conversion differences are function eta and proof
irrelevance. Any other unexpected semantic difference, parser failure, missing
result, failed resource control, or source mismatch fails the comparison. Work
budgets and cache accounting differ across implementations; finite comparison
does not establish exact resource-accounting correspondence.

The compiler and comparison repository remain external pinned checkouts. Their
complete Git archive hashes, revisions, and consumed-file hashes are verified.
Generated C is a temporary derived artifact whose identity is recorded. No
third-party checker or estate auditor is vendored here. The external native Lean
comparison and the local Lean proof lane have separate purposes and evidence.

## Promotion conditions

Introducing an accepting boundary requires a reviewable change that names the
boundary, its contract and existing implementation files, defines the trusted
base and supported semantics, supplies rejection and correspondence evidence,
and changes the manifest under the applicable estate authority decision. A
boundary may span multiple implementation languages. Adding executable code
alone does not grant authority.

Broader Lean compatibility requires implementing and testing the missing kernel
features. Performance results do not establish those semantics. The estate
position and candidate stage remain unchanged, and
`origin.decided_by = "proposed"` records that no separate estate-wide adoption
decision is asserted. Local v3 adoption does not register the repository in the
global estate registry.

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
| `formal/` | Lean transaction and full-record binding proofs, executable models, and Quint checks |
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

## Formal transaction and stored-binding boundary

Both required scopes map to `check_definition` in the Goose reference. The
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
Its complete raw DAG schema can describe more syntax than the Sort/Const payloads
covered by the current correspondence profile. General correctness of the trace
adapter, arbitrary-expression correspondence, and refinement of the checker by
the models remain open. The complete claims, required inventories, and limits
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

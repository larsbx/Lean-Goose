# Authority and architecture

Lean-Goose is a candidate research repository for a bounded Goose reference.
It owns no theorem, declaration, operational or deployment admission boundary.
The canonical language declaration identifies Goose as this project's language
for a future local kernel; no such kernel is implemented in this scaffold.
`acceptance_authority = false` therefore remains explicit.

## Authority before language

| Plane | Implemented role |
| --- | --- |
| `policy/` | Scaffold governance, evidence and publication policy |
| `kernel/` | Boundary notice for the unimplemented admission kernel |
| `reference/` | Locally owned, bounded Goose checking observations |
| `oracles/` | Contract for pinned external Lean and OCaml comparisons |
| `schemas/` | Versioned input and observation contracts |
| `conformance/` | Source identities, dependency pins and generated observations |
| `tools/` | Builds, external source verification, comparison and receipts |
| `docs/` | Reproduction, historical results and next obligations |

The repository is one program. Unused proof, experiment, vendor, application or
paper directories are not created. Moving the prototype here does not change
its authority or make a finite comparison a proof.

## Owned reference

`reference/checker.goose` is an explicitly adopted derivative of the Goose
prototype in Lean-OCaml at the recorded source commit. The scaffold changes
presentation-only observation labels and output schema IDs. It does not change
inference, substitution, normalization, caching or resource limits. Provenance
records the original file identity, exact replacements and local file digest.

The checker validates bounded syntax and observes success or a designated
refusal for transparent monomorphic definitions. Its success label is
`observed_success`; it emits `acceptance_authority: false`. A test `passed`
status means the observed behavior matches a registered finite expectation.
It conveys no domain admission or mathematical proof verdict.

## External comparison boundary

Goose, Lean and OCaml receive identical generated DAG inputs. The trusted Lean
process performs its own native checked declaration insertion at trust level
zero. That process's authority stays with Lean. The adapter maps external
success observations to this repository's observation vocabulary before saving
or emitting local evidence.

The two explicitly registered conversion differences are function eta and proof
irrelevance. Any other unexpected semantic difference, parser failure, missing
result, failed resource control or source mismatch fails the comparison. Work
budgets and cache accounting differ across implementations; successful finite
checks do not establish exact resource-accounting correspondence.

The compiler and comparison repository remain external pinned checkouts. Their
complete Git archive hashes, revisions and consumed-file hashes are verified.
Generated C is a temporary derived artifact whose identity is recorded. No
third-party implementation or estate auditor is vendored here.

## Promotion conditions

Introducing an authoritative kernel requires a separate, reviewable change
that names its exact input/output boundary and sole implementation, defines
its trusted base and supported semantics, supplies rejection and correspondence
evidence, and changes the manifest under the applicable estate authority
decision. Broader Lean compatibility requires implementing and testing the
missing kernel features; benchmark speed cannot satisfy those conditions.

This scaffold uses the template's default research position and initial candidate
stage. `origin.decided_by = "proposed"` records that no separate estate-wide
adoption decision is asserted. A local layout audit does not register the
repository in the global estate registry.

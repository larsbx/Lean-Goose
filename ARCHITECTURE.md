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
| `formal/` | Lean transaction proofs, executable model, and Quint checks |
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
prototype in Lean-OCaml at the recorded source commit. The source adaptation
changes presentation-only observation labels and output schema IDs. Its checking
algorithm, substitution, normalization, caching, and resource limits remain the
recorded derivative. Provenance records the original file identity, exact
replacements, and local file digest.

The checker observes success or a designated refusal for transparent monomorphic
definitions. Its success label is `observed_success`; its output declares
`acceptance_authority: false`. A test `passed` status means the behavior matches
a registered finite expectation. The local observation protocol confers no
domain admission rights.

## Formal transaction boundary

The first formal scope models ordered definition insertion. It captures the
priority of duplicate-name checks, insertion only after success, preservation of
the environment on designated refusals, and the absence of a completed receipt
when scope checking terminates execution. It also relates the number of successful
observations to the model's environment size and preserves its lack of authority.

The implementation mapping is to `check_definition` and `check_only` in the Goose
reference, with observation validation in `tools/run.py`. The model abstracts
expression checking into four action classes. Its names and environment are
mathematical values; the runtime adapter encodes a finite set as actual DAG inputs.

Lean proves properties for arbitrary finite action traces. Quint provides an
independently written executable model, deterministic tests, bounded simulation,
and an unsafe-transition counterexample. Finite comparison checks the Lean and
Quint models and the observable Goose output for a declared input inventory.
The complete claims, assumptions, mappings, and limits are in
[docs/formalization.md](docs/formalization.md).

The runtime does not expose its environment representation. Equality of the
models' full states is distinct from agreement with Goose's observable ordered
outcomes, success count, and fatal-process behavior. Full refinement of the
Goose implementation remains open.

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

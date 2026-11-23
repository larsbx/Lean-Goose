# Semantic environment increment: review and publication record

## Outcome and source identity

All required local `make acceptance` gates passed on November 23, 2026.
The run lasted from 2026-11-23T11:15:41.479009+00:00 to 2026-11-23T11:29:59.831249+00:00.
The user authorized a PR against `main`, merge, roadmap updates and beginning
these next obligations. Subsequent publication and hosted status belong to the
PR and GitHub Actions; this document records local execution evidence.

| Identity | Value |
| --- | --- |
| Base main | `c79bafddb6372decf1a373c14c4c8eb7ec4eea3e` |
| Tested local source revision | `92c9c07b3bcc4e408a1ce4bb81b7ba34ec355346` |
| Tested source Git tree | `247c6c0c5caa9756f2eecdb2f1853b0f36375af1` |
| Source manifest SHA-256 | `0fa93f85941c64b99d1641bd19a374b599f1ec8d17a3c661e70f6b1f53af578b` |
| Source inventory | 90 files; unchanged throughout and after verification |
| Source branch | `formal/semantic-environment` |

Publication through the connected GitHub Git-data API can assign different
commit IDs. Its published source and evidence trees must match the local Git
trees exactly. The publication commits and PR record that mapping. Original
acceptance receipts retain their tested local source identity.

## Proof increment

`BindingValidIn` contains independent predecessor judgments: the original type
and value are closed and use available constants; the declared type has a sort;
the original value infers some actual type that normalizes to the stored
inferred field; and that field converts to the original declared type.
`Certified` builds the ordered environment by fresh, certified insertion.

The new development proves lookup-preserving weakening of head reduction,
normalization, conversion, inference and sort judgments. Consequently, an old
binding's semantic derivations hold in the final environment, not merely its
historical predecessor. Success/refusal and arbitrary finite processed traces
preserve certification, complete earlier lookups and record prefixes.

The projection into `GooseStoredBindings.Binding` retains all three encoded
expression fields and directly uses the earlier indexed-record preservation
lemma. Lookup correspondence explicitly assumes injective name coding. It does
not simulate the older four-action checker or equate different constant wires.

The new namespace audit checked 80 declarations, including 45 theorem
declarations. All 37 required theorem closures are empty; the entire new
namespace uses no axioms. The five preceding model sources, owned checker,
derivation sources and external pins remain unchanged.

## Executed verification

| Gate or profile | Observed result |
| --- | --- |
| Required repository gates | Estate audit, Python controls, formal, conformance and benchmark smoke passed |
| Python controls | 126 passed, including ten new exact-negative-witness test groups |
| Lean obligations | 181 across six scopes, including 37 new axiom-free obligations |
| Quint deterministic tests | 129 across six scopes, including 24 new tests |
| Quint invariants and controls | Six sampled invariant runs and six exact negative witnesses passed |
| New Quint exploration | 1,000 samples, at most eight transitions and four snapshots, three names/nine forms, seed 20261123 |
| New history profile | 12 cases, 62 input definitions, 61 processed snapshots, 24 native trace/check commands |
| New external comparison | Ten fixtures; 52 ordered outcomes per Goose/Lean/OCaml engine; no new disagreements |
| Retained comparisons | 964 earlier ordered outcomes and 59 typing outcomes per engine, separately retained |
| Retained substitution | 2,546 model/native operation comparisons plus existing controls |
| Retained formal scopes | All five preceding scopes and negative controls passed |
| Formal command evidence | 227 recorded command executions with hashed logs |
| Source/dependencies/tools | Unchanged before/after identities |
| Smoke | Seven workload families, three engines, one sample/eight definitions; no performance claim |
| Hosted evidence for this increment | Separate from this local record; inspect its exact PR/head run |

The new model/native histories use the unchanged actual typing replay helpers.
Native Goose exposes stored records and raw IDs, not semantic proof certificates.
External Lean/OCaml expose ordered definition outcomes, not full stored fields.
These finite comparisons do not establish general implementation refinement.

The previous accepted [PR #6](https://github.com/larsbx/Lean-Goose/pull/6)
has a successful [hosted main run](https://github.com/larsbx/Lean-Goose/actions/runs/45079151056)
at `c79bafddb6372decf1a373c14c4c8eb7ec4eea3e`. Its historical receipts and review manifests are interpreted at
that immutable revision, not relabeled as this run's evidence.

## Next precise obligation and proof route

The [roadmap](../../docs/roadmap.md) now names
`checked_success_inferred_closed_available`: from `Certified E` and
`checked fuel E d = .ok A`, derive `Closed A` and `Available E A`.

A read-only follow-up review identified a minimal route. For a newest-first
context, a domain stored at index `i` should be scoped at depth
`context.length - i - 1` and have available constants. Variable inference lifts
that domain by `i + 1`. Merely allowing every domain the full current context
depth is insufficient. Prove availability preservation under lift/substitution,
then scope/availability preservation for relational reduction, normalization and
inference. Existing certified lookup validity supplies closed/available stored
original types and values. This syntactic target need not wait for full
`HasSort` validity of binder contexts or a sufficient-fuel theorem.

No implementation of this next target is claimed here. Full context metatheory,
typed substitution and beta/zeta preservation, sufficient-budget completeness,
normalization, concrete name encoding, native semantic/resource/cache refinement
and serializer/compiler/parser boundaries remain open. Eta, proof irrelevance,
general universes, inductives and other unsupported features retain their
boundaries. `acceptance_authority` remains `false`.

## Review links

- [Source patch](semantic-environment-proposal.patch)
- [Semantic environment specification](../../docs/semantic-environment.md)
- [Lean proofs](../../formal/lean/SemanticEnvironment.lean)
- [Quint checks](../../formal/quint/SemanticEnvironment.qnt)
- [Repository acceptance receipt](verification.json)
- [Formal receipt](formal/results.json)
- [Conformance receipt](check/results.json)

# Lean-Goose typing/conversion proposal: review record

## Outcome

The local proposal passed every required `make acceptance` gate on the corrected
source revision below. The run completed on November 22, 2026,
05:17:13 PM–05:29:35 PM EST. This record was prepared before publication.
The user subsequently authorized opening the PR against `main` and merging it.
The recorded results below remain local verification; PR metadata and GitHub
Actions provide the later publication, merge and hosted-check status.

| Identity | Value |
| --- | --- |
| Base main revision | `632ab16805830aaf8ee94a4647dc948901e09423` |
| Tested source revision | `3718d12fbe977ed322faa10fe81143b3ddbcb0f3` |
| Source manifest SHA-256 | `9f167c6549e77d58a60b540baca0cda5b4c8ca3307e2ed0917e7c9596a8422d4` |
| Source inventory | 82 files; unchanged during and after verification |
| Local branch | `review/typing-conversion` |
| Proposed source diff | 22 files; 3,147 insertions and 44 deletions |

## Proof increment

The proposal reuses the established expression DAG, scope, lifting and
capture-avoiding substitution definitions. It adds numeric-sort inference for
all seven existing constructors and beta/zeta reduction with transparent delta.
The independent Lean judgments are `HeadReduces`, `Normalizes`, `Converts`,
`Infers`, and `HasSort`.

Successful executable model inference derives `Infers`; successful sort
checking derives `HasSort`. Successful definition checking establishes that the
declared type has a sort, that the original value has an inferred type which
normalizes to its stored inferred field, and that this stored field converts to
the original declared type. A successful insertion retains the original declared
type and value; a refusal retains all existing bindings.

The complete new namespace audit covers 351 declarations, including 148 theorem
declarations. All 32 required named theorems have empty transitive axiom
closures. Generated support is permitted only `propext`.

## Executed verification

| Check | Final observed result |
| --- | --- |
| Required repository gates | Estate audit, Python controls, formal verification, conformance and benchmark smoke all passed |
| Python controls | 116 passed, including repeat-run evidence-directory reuse |
| All five Lean scopes | 144 required theorems passed; four established scopes retained |
| All five Quint scopes | 105 deterministic tests; five sampled invariant runs and five exact negative witnesses passed |
| New Quint scope | 26 tests; 1,000 samples with at most eight transitions and four processed snapshots |
| New model/native profile | 48 requests, 67 definitions, 66 processed snapshots; one later definition intentionally suppressed after a fatal scope result |
| New native executions | 96 commands across trace and check modes |
| New strict replay refusals | 24 malformed requests rejected by each actual helper; 48 refusal executions |
| New model budget controls | Both actual helpers report code 9 distinctly; native comparison cannot accept it |
| New common-reference comparison | 44 fixtures, 59 ordered outcomes per engine, actual Goose / Lean / OCaml; no new semantic disagreements |
| Retained comparison | 964 ordered outcomes per engine, existing eta/proof-irrelevance boundaries, six structural/resource controls |
| Retained DAG replay | 11,947 distinct native arenas replayed by both actual models |
| Retained substitution replay | 2,546 Lean/Quint/native operation comparisons; established native controls retained |
| Smoke | Seven families, three engines, eight definitions, one timing sample per configuration; no new performance claim |
| Provenance | Source/dependency identities and formal tool executables remained unchanged |
| Hosted CI | No hosted result for this unpublished proposal |

The earlier complete pass at `b8b53413a1fb735d244579897ae9157aa071a6b2`
is retained under `formal-attempts/typing-initial-pass/`, bound to its own source
manifest. A final review found that its new comparison directory creation would
fail on a second run. The corrected revision reuses the directory, overwrites
stale fixtures, and executes all engines again. A targeted regression test and
the complete fresh acceptance above verify the correction.

## Evidence and source review

- [Complete source proposal patch](typing-conversion-proposal.patch)
- [Detailed proof scope and obligations](../../docs/typing-conversion.md)
- [Replay contract](../../schemas/typing-conversion-replay-v1.md)
- [Lean model and proofs](../../formal/lean/TypingConversion.lean)
- [Independent Quint model](../../formal/quint/TypingConversion.qnt)
- [Repository receipt](verification.json)
- [Formal receipt](formal/results.json)
- [Three-engine conformance receipt](check/results.json)

## Limits and next proof

This is successful-execution soundness of the model against its independent
operational judgments, plus finite implementation correspondence. External
Lean/OCaml drivers expose ordered outcomes, not the Goose stored-field trace.
The model's recursion budget and Quint's 2,048-transition machine cap are
separate from native work, height, index and allocation limits.

The next focused proof is preservation of a well-formed semantic environment
across successful definition traces, linked explicitly to the earlier generic
stored-binding model. Further work includes sufficient-budget completeness,
normalization and typed reduction preservation for an admissible fragment,
refinement of actual Goose transitions/caches/resources, and broader
correspondence with Lean's kernel semantics. Eta, proof irrelevance, general
universe expressions, inductives, recursors, quotients and other unsupported
features retain their boundaries. Admission authority remains false.

After reviewing this proposal, the user instructed: "Open the PR against main
and merge." This authorizes publication and merge subject to actual repository
protections. The generated acceptance receipts have not been edited; this
publication note only records the subsequent authorization.

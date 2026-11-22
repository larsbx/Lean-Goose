# Next concrete obligations

The required formal scope includes ordered-name transactions, complete
stored-binding preservation, structural expression DAGs with binder scope,
capture-avoiding lifting/substitution, and numeric-sort typing with beta/zeta/delta conversion.
The original 1,110-case and 2,954-case lanes remain. The
[DAG lane](expression-dag-scope.md) connects all seven raw node kinds to
structural expressions, proves recursive scope laws, and adds native probes at
four binder depths plus malformed topology and context controls.
The [substitution lane](substitution.md) adds scope and index laws, arbitrary
nested-lambda noncapture, and direct comparisons with actual Goose `lift` and
`substitute`, including capture, malformed-scope, and resource controls.
The [typing/conversion lane](typing-conversion.md) connects successful model
evaluation to independent typing/reduction judgments, compares compound stored
fields and refusals against native Goose, and adds common-fragment outcome
comparisons with pinned Lean and OCaml. General implementation refinement is
still separate from this model soundness and finite evidence.
The proof scope and required execution inventories are in
[formalization.md](formalization.md). A particular revision is verified only when
its matching execution receipt records the required gates as passed.

1. **Typing metatheory and semantic environments:** define well-formed bindings
   and contexts, prove their preservation across successful traces, and connect
   this semantic environment to the earlier full-record model. Then establish
   sufficient-budget completeness, deterministic normal forms and typed
   beta/zeta preservation for a precisely stated admissible fragment.
   Successful model inference already derives the independent rules; general
   completeness and native correspondence are not consequences of that result.
   Eta, proof irrelevance and unsupported Lean features retain their boundaries.
2. **Implementation refinement:** prove the relation between model transitions,
   concrete binding lookup, DAG decoding, and the native checker. The present
   Lean statements preserve arbitrary model records and define structural DAG
   decoding, scope, lifting, substitution, and typing/reduction soundness;
   native comparison remains finite. Refine concrete inference, validation,
   conversion and error behavior as well as transformations.
   Prove refinement of the actual transformation functions and their metadata
   optimizations. Add evidence for the diagnostic
   serializer and its snapshot timing without treating diagnostic output alone
   as a proof of the implementation.
3. **Resource and cache behavior:** model work, height, intermediate-node, and
   context limits, including failure priority around duplicate and semantic
   checks. Specify which caches remain valid across insertion or refusal.
   Diagnostic trace bounds and checker resource limits are separate contracts;
   existing cache state, contexts, and fuel are outside the stored-binding model.
4. **Fresh unshared syntax:** profile arena import, metadata construction, and
   inference on `unshared_trees`. Preserve all five formal scopes, full positive and
   refusal conformance, and trace compatibility when optimizing representations
   or caches. Re-run the full performance experiment on the new source revision
   before making a new speed claim.
5. **Module separation:** split checking semantics from observation, diagnostic,
   and timing adapters under source-bound replay. Preserve both the original
   checking/parser source relationship and the explicit formal implementation
   mappings, or document and verify any intended semantic change.
6. **Accepting-boundary proposal:** before introducing an authoritative entrypoint,
   name its exact contract and implementation files, trusted base, supported
   semantics, rejection evidence, and formal obligations. Review the manifest
   authority change explicitly. Implementation languages remain unrestricted;
   proofs, comparisons, diagnostics, and performance measurements do not grant
   declaration, theorem, operational, or deployment admission authority.

General universes, inductives, recursors, quotients, `.olean` ingestion, and full
Lean theorem admission remain outside the reference. The retained 964-outcome
comparison, structural/resource controls, and benchmark smoke continue to serve
their stated finite validation roles alongside the formal work.

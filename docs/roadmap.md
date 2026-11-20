# Next concrete obligations

The required formal scope includes ordered-name transactions, complete
stored-binding preservation, structural expression DAGs with binder scope,
and capture-avoiding lifting/substitution.
The original 1,110-case and 2,954-case lanes remain. The
[DAG lane](expression-dag-scope.md) connects all seven raw node kinds to
structural expressions, proves recursive scope laws, and adds native probes at
four binder depths plus malformed topology and context controls.
The [substitution lane](substitution.md) adds scope and index laws, arbitrary
nested-lambda noncapture, and direct comparisons with actual Goose `lift` and
`substitute`, including capture, malformed-scope, and resource controls.
The proof scope and required execution inventories are in
[formalization.md](formalization.md). A particular revision is verified only when
its matching execution receipt records the required gates as passed.

1. **Typing and conversion correspondence:** extend the formal mapping to
   inference and beta/zeta reduction for the supported fragment. Exercise stored
   type/value/inferred fields for compound expressions and verify rejection
   behavior as well as successful cases. Eta, proof irrelevance, and unsupported
   Lean features retain their explicit boundaries until separately implemented.
2. **Implementation refinement:** prove the relation between model transitions,
   concrete binding lookup, DAG decoding, and the native checker. The present
   Lean statements preserve arbitrary model records and define structural DAG
   decoding, scope, lifting, and substitution; native comparison remains finite.
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
   inference on `unshared_trees`. Preserve all four formal scopes, full positive and
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

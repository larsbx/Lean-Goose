# Next concrete obligations

The required formal scope now includes ordered-name transactions and complete
stored-binding preservation. The original 1,110-case lane remains, and the new
2,954-case profile connects model snapshots to bounded native `--trace` and
`--check` observations. The proof scope and required execution inventories are in
[formalization.md](formalization.md). A particular revision is verified only when
its matching execution receipt records the required gates as passed.

1. **Expression representation and scope:** define the correspondence between
   raw node IDs, the immutable DAG, and structural expressions beyond Sort/Const.
   Cover applications, Pis, lambdas, typed lets, and de Bruijn variables; preserve
   sharing and identify the exact scope assumptions at import and lookup.
2. **Capture-avoiding substitution:** prove the selected lifting and substitution
   laws, including binder cutoffs, index shifting, and scope preservation. Connect
   those definitions to Goose `lift` and `substitute`, with concrete capture and
   malformed-scope controls. The current transaction models abstract these
   operations into action classes.
3. **Typing and conversion correspondence:** extend the formal mapping to
   inference and beta/zeta reduction for the supported fragment. Exercise stored
   type/value/inferred fields for compound expressions and verify rejection
   behavior as well as successful cases. Eta, proof irrelevance, and unsupported
   Lean features retain their explicit boundaries until separately implemented.
4. **Implementation refinement:** prove the relation between model transitions,
   concrete binding lookup, DAG decoding, and the native checker. The present
   Lean statements preserve arbitrary model records, while native comparison
   covers a finite Sort/Const inventory. Add evidence for the diagnostic
   serializer and its snapshot timing without treating diagnostic output alone
   as a proof of the implementation.
5. **Resource and cache behavior:** model work, height, intermediate-node, and
   context limits, including failure priority around duplicate and semantic
   checks. Specify which caches remain valid across insertion or refusal.
   Diagnostic trace bounds and checker resource limits are separate contracts;
   existing cache state, contexts, and fuel are outside the stored-binding model.
6. **Fresh unshared syntax:** profile arena import, metadata construction, and
   inference on `unshared_trees`. Preserve both formal scopes, full positive and
   refusal conformance, and trace compatibility when optimizing representations
   or caches. Re-run the full performance experiment on the new source revision
   before making a new speed claim.
7. **Module separation:** split checking semantics from observation, diagnostic,
   and timing adapters under source-bound replay. Preserve both the original
   checking/parser source relationship and the explicit formal implementation
   mappings, or document and verify any intended semantic change.
8. **Accepting-boundary proposal:** before introducing an authoritative entrypoint,
   name its exact contract and implementation files, trusted base, supported
   semantics, rejection evidence, and formal obligations. Review the manifest
   authority change explicitly. Implementation languages remain unrestricted;
   proofs, comparisons, diagnostics, and performance measurements do not grant
   declaration, theorem, operational, or deployment admission authority.

General universes, inductives, recursors, quotients, `.olean` ingestion, and full
Lean theorem admission remain outside the reference. The retained 964-outcome
comparison, structural/resource controls, and benchmark smoke continue to serve
their stated finite validation roles alongside the formal work.

# Next concrete obligations

## Accepted starting point

[PR #6](https://github.com/larsbx/Lean-Goose/pull/6) merged the numeric-sort
typing and beta/zeta/delta conversion increment into `main` through
`c79bafddb6372decf1a373c14c4c8eb7ec4eea3e`. Its published source revision
`f45bb43d5c5ce15dd335a5f7ae2915fb581cc3ca` has the exact Git tree of locally
tested source `3718d12fbe977ed322faa10fe81143b3ddbcb0f3`. The
[hosted main run](https://github.com/larsbx/Lean-Goose/actions/runs/45079151056)
completed successfully on the merge revision. The original local receipts
retain their own source identity.

The five retained scopes establish ordered-name transactions, complete
stored-record preservation, expression-DAG representation and binder scope,
capture-avoiding lifting/substitution, and successful typing/conversion model
soundness. Their finite native observations remain distinct from general
implementation refinement or full Lean kernel compatibility.

## Semantic environments, stored-field scope, and the record bridge

The [semantic-environment increment](semantic-environment.md) adds independent
certificates for the original declared type/value and normalized inferred
field in each binding's exact predecessor environment. It proves that fresh
insertion and refusal preserve certification across arbitrary finite traces.
Lookup-preserving environment weakening transports the relational typing and
reduction judgments into the final environment, so old certificates remain
valid after later insertions.

The projection to `GooseStoredBindings.Binding` retains every encoded payload
and directly reuses the earlier indexed-record preservation theorem. Lookup
correspondence has an explicit injective name-coding premise; this does not
equate the earlier four-action checker with compound-expression typing.

[PR #7](https://github.com/larsbx/Lean-Goose/pull/7) merged those results through
`8ded5c39faa52ad58743d7c5fdfe09049398ed62`. The extended sixth scope proves
`checked_success_inferred_closed_available` from `Certified` and successful
checking. Its weaker version requires closed original values from lookup.
Every processed snapshot and the final environment preserve scope and constant
availability for all three fields. Binder-context validity uses each entry's
outer tail. The structural portion suffices for scoped inference.

The [typed context weakening increment](context-weakening.md) transports exact
`Infers` outputs and `HasSort` levels under arbitrary single-binder insertion.
It also preserves context validity, handles the selected-variable substitution
case up to conversion, and proves immediate zeta preservation.

## Ordered next proof work

1. **Typed substitution and reduction preservation.**
   Transport newer annotations across substitution in their outer tails.
   Establish the head/normalization and conversion laws needed by the Pi,
   application and sort cases. Prove relational substitution up to conversion,
   an inferred-type sort witness, and preservation for beta and subsequent
   reductions after zeta. Relate delta preservation to the original stored
   type and value.
2. **Determinacy, conversion and sufficient budgets.** Prove deterministic
   normal forms and the required conversion laws, then connect derivations to
   executable inference/normalization with a sufficient budget. State the
   admissible environment, context, and term hypotheses. Prove normalization
   for all inputs in the specified typed fragment and existence of enough
   successful fuel.
3. **Concrete record and name representation.** Discharge injectivity for the
   chosen concrete name encoding over its declared ASCII domain and connect
   structural encoded records to native DAG IDs and lookup. Keep exact record
   preservation separate from a simulation of the older abstract action model.
4. **Native semantic refinement.** Relate the proved model transitions to the
   actual Goose inference, validation, conversion, binding lookup, lifting and
   substitution implementations. Prove the concrete DAG/metadata relation and
   diagnostic serializer/snapshot timing. Present finite replay remains
   evidence about its selected inputs; it is not that refinement theorem.
5. **Resources, caches and failure priority.** Model native work, height,
   intermediate-node and context limits, and specify cache validity across
   insertion/refusal. Distinguish model recursion fuel, Quint's evaluator cap,
   native limits and diagnostic envelopes. Prove which error priorities hold
   under which resource assumptions.

## Later engineering and authority decisions

- **Fresh unshared syntax:** profile arena import, metadata construction and
  inference on `unshared_trees`. Preserve all six formal scopes, positive and
  refusal conformance, and trace compatibility when optimizing. Rerun the full
  performance experiment on its exact source before making a new speed claim.
- **Module separation:** split checking semantics from observation, diagnostic
  and timing adapters under source-bound replay. Preserve the checking/parser
  provenance and explicit formal implementation mapping, or document and
  verify an intended semantic change.
- **Accepting-boundary proposal:** before introducing an authoritative
  entrypoint, name its contract, implementation, trusted base, supported
  semantics and rejection evidence; review the manifest authority change
  explicitly. Implementation languages remain unrestricted. Proofs, diagnostic
  observations and performance measurements grant no admission authority.

The required inventories are in [formalization.md](formalization.md). The
original 1,110-case and 2,954-case lanes, all DAG/scope and 2,546 substitution
comparisons, previous typing cases, 964 ordered outcomes, existing
eta/proof-irrelevance differences, resource controls and benchmark smoke remain
required. Local and hosted results must each identify the exact source tested.

General universes, eta, proof irrelevance, inductives, recursors, quotients,
`.olean` ingestion, and full Lean theorem admission remain outside the reference.
The repository continues to have `acceptance_authority = false`.

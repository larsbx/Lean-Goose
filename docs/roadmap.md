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

## Begun here: semantic environments and the record bridge

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

The required increment is 37 Lean obligations, 24 Quint tests, bounded invariant
exploration and an exact old-record corruption witness. Twelve additional
native/model histories cover 62 definitions and 61 processed snapshots; ten
common-reference histories add 52 ordered outcomes per engine. These are gate
requirements. Their executed status belongs to the matching new source-bound
receipt, not to the earlier PR #6 result.

## Ordered next proof work

1. **Inferred-field scope and well-formed contexts.** Define binder-context
   validity using the existing de Bruijn orientation: each entry must have a
   sort in its preceding outer context. Prove that certified environments and
   valid contexts preserve scope and constant availability through inference
   and normalization. The first named target is a successful-check theorem
   `checked_success_inferred_closed_available`: from `Certified E` and
   `checked fuel E d = .ok A`, derive `Closed A ∧ Available E A`.
   The present certificate proves these properties for the original
   type/value, and gives derivations for the inferred field; it does not yet
   independently prove its scope/availability. Add dependent-context and
   rejected-context controls while retaining all six scopes.
2. **Typed substitution and reduction preservation.** Build the context
   weakening and substitution lemmas over the existing capture-avoiding
   operations. State the type relation explicitly, including conversion where
   required, before proving beta and zeta subject reduction for the admitted
   fragment. Do not replace this obligation with structural substitution laws.
3. **Determinacy, conversion and sufficient budgets.** Prove deterministic
   normal forms and the required conversion laws, then connect derivations to
   executable inference/normalization with a sufficient budget. State the
   admissible environment/context/term hypotheses. Termination of a function
   for a supplied budget is already provided by Lean; normalization of all
   well-typed inputs and existence of enough successful fuel remain open.
4. **Concrete record and name representation.** Discharge injectivity for the
   chosen concrete name encoding over its declared ASCII domain and connect
   structural encoded records to native DAG IDs and lookup. Keep exact record
   preservation separate from a simulation of the older abstract action model.
5. **Native semantic refinement.** Relate the proved model transitions to the
   actual Goose inference, validation, conversion, binding lookup, lifting and
   substitution implementations. Prove the concrete DAG/metadata relation and
   diagnostic serializer/snapshot timing. Present finite replay remains
   evidence about its selected inputs; it is not that refinement theorem.
6. **Resources, caches and failure priority.** Model native work, height,
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

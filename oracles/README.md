# External comparison engines

Comparison code is read from `larsbx/Lean-OCaml` at the exact revision in
`conformance/dependencies.json`. The checkout is outside this repository and is
verified before use. `LEAN_OCAML_SOURCE` may name an existing clean checkout;
otherwise the runner fetches a temporary pinned copy.

The consumed sources supply the original fixture generators, committed typing
and definition vectors, OCaml bytecode observers and native Lean observer. The
Goose binary is always compiled from this repository's
`reference/checker.goose`. Substituting the upstream Goose file would fail to
test the local derivative and is outside the runner's contract.

The adapter checks complete ordered outcomes against registered expectations.
It translates the legacy external success label to `observed_success` and
records `acceptance_authority: false` locally. External checking authority stays
with its owner. The two specific eta/proof-irrelevance differences are registered;
unexpected disagreement, an unclassified error or a resource failure fails the
comparison.

The dependency inventory identifies each consumed path, its SHA-256 and the
source archive identity. No external implementation is vendored in this plane.

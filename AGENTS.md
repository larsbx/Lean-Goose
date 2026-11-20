# Working on Lean-Goose

Read `ARCHITECTURE.md`, `ESTATE.toml` and the relevant schema before changing
semantics. This is a bounded reference with no admission authority. Preserve
the observation vocabulary and the distinction between computation and proof.

Keep external compilers, reference implementations and the estate auditor in
pinned external checkouts. Use the recorded archive/file hashes and verify
provenance before executing comparisons. Never edit supplied toolchain or
baseline checkouts to make tests pass.

For semantic, parser, cache, resource or output-contract changes, update the
registered positive and refusal cases, document the intended difference, and
run `make acceptance`. Generated evidence must come from that run; do not edit
results to manufacture success. Record the exact source identity, local result
and hosted status separately. Historical benchmark results belong to their
recorded source and must not be relabeled as fresh measurements.

Keep changes in their authority plane. A future kernel or promotion requires an
explicit boundary decision and manifest update. Repository layout conformance
does not establish estate-wide membership or broader Lean compatibility.

Publish changes through a branch and PR against `main`. Honor the user's
publication and merge instructions, actual repository protections and current
check results. A queued or missing hosted check is not a successful check.

This is locally authored project guidance. It is not a generated agent-icm
template or a claim of registry enrollment.

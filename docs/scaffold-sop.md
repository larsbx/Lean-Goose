# Repository SOP and adoption history

The repository is [larsbx/Lean-Goose](https://github.com/larsbx/Lean-Goose), GitHub
repository ID **1464997572**, with default branch `main`. The initial main
revision was `bdd46cb86f3adcd3ed80f0b29e3759250436c5b0` and contained only the
repository heading.

## Current v3 contract

The repository now adopts estate-repository-v3 at governance revision
`b851c92fceb88c8e6f4604664cf975b567ade161`, following the revised owner direction
recorded in governance DR-0006. Implementation languages are unrestricted.
Authority is explicitly `false`; both Lean and Quint formalization are required
for the declared scope.

The governance checkout's `tools/pin_estate.py` establishes the external auditor
pin. Its SHA-256 is verified before execution. The formal gate separately checks
actual proofs, model obligations, finite runtime correspondence, toolchains,
and source identities. A layout pass alone does not establish executed formal
verification.

The research position and candidate stage remain in place.
`origin.decided_by = "proposed"` avoids asserting an estate-wide adoption
decision that this repository does not contain. The global registry and its
generated adopter table are separate governance artifacts.

## Historical scaffold

[PR #1](https://github.com/larsbx/Lean-Goose/pull/1) introduced the standalone
reference under estate-repository-v2, pinned to
`bd731398b567cfe523667fc8e23a96d299067141`. Its merge revision is
`fa34fb379c543073d08a4ba6ea6f87d291b90a99`. The former canonical-language table
and placeholder kernel notice belonged to that v2 scaffold. They do not impose
language requirements on the current v3 contract.

Original extraction provenance and benchmark source identities remain recorded.
Adopting v3 does not relabel those historical measurements as a fresh benchmark.

## Publication

Project documentation, workflow, and PR guidance here are locally authored.
The repository does not claim generated agent-icm templates or registration in
that system. Adopted executable source has its own exact provenance.

Publish through a branch and PR against `main`, following the user's instructions,
actual protections, and current check results. A merge must use the inspected
PR head, preserve recorded evidence, and be verified against the resulting main
revision. A queued or missing hosted check is not a successful result. Publication
preserves the reference's declared lack of admission authority.

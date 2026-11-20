# Implementation and verification inventory

Estate-repository-v3 permits any implementation language or combination. This
table records the current implementation. Authority is declared at the repository
and boundary level in `ESTATE.toml`.

| Language | Location | Current role |
| --- | --- | --- |
| Goose | `reference/checker.goose` | Locally owned bounded reference and observation adapter |
| Lean | `formal/lean/` | Transaction model, proofs, axiom audit, and executable replay |
| Lean | Pinned external comparison checkout | Native checked declaration insertion used for finite comparison |
| Quint | `formal/quint/` | Executable transaction model, invariant checks, tests, and counterexample control |
| OCaml | Pinned external comparison checkout | Bytecode reference used for independent finite comparisons |
| Python | `tools/`, `tests/` | Dependency checks, fixture orchestration, formal gates, and unsigned receipts |
| Shell | `tools/*.sh`, CI | Compiler builds and pinned auditor execution |
| C | Temporary generated build directory | Derived Goose output and external timing support, identified by hashes |

All supported expression-checking rules in the local reference originate in
Goose source. Its generated C and native backend retain the same declared lack
of admission authority.

Source history from Lean-OCaml remains attributed by immutable repository,
commit, path, Git blob, and SHA-256. Comparison code is consumed from its pinned
external checkout. The local formal sources are separately owned artifacts
whose scope and correspondence limits are documented in
[docs/formalization.md](docs/formalization.md).

Lean and Quint are required verification technologies for v3. Neither their use
nor a successful benchmark promotes the repository to an accepting boundary.
`[authority].acceptance_authority` remains `false`.

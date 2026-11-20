# Language boundaries

| Language | Location | Role |
| --- | --- | --- |
| Goose | `reference/checker.goose` | Locally owned bounded reference and observation adapter; planned kernel language |
| Lean | Pinned external comparison checkout | Trusted native checking performed externally; local results remain evidence |
| OCaml | Pinned external comparison checkout | Bytecode reference used for independent finite comparisons |
| Python | `tools/` | Dependency checks, fixture orchestration and unsigned receipts |
| Shell | `tools/*.sh`, CI | Reproducible compiler builds and pinned audit execution |
| C | Temporary generated build directory | Derived Goose output and existing external timing support, identified by hashes |

The native C backend does not confer additional authority. All supported
expression-checking rules in the local reference originate in Goose source.
No locally handwritten C checker replaces those rules.

Source history from Lean-OCaml remains attributed by immutable repository,
commit, path, Git blob and SHA-256. Comparison code is consumed from its pinned
external checkout instead of being copied under local ownership.

Exactly Goose is canonical in `ESTATE.toml`. Every language has
`acceptance_authority = false`; the repository has no admission boundary.

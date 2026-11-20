# Lean-Goose: bounded Lean migration reference

Goose implementation of the bounded expression-checking fragment used by the
Lean kernel migration experiments. This repository owns the Goose reference;
the native Lean and OCaml bytecode comparison engines are pinned external
dependencies. The reference produces observations and has no declaration,
theorem, deployment or other admission authority.

The initial implementation is derived from
[Lean-OCaml PR #8](https://github.com/larsbx/Lean-OCaml/pull/8) at
`403dcca50d7e8f18954618eec72109f8cb1c6b61`. The local adaptation changes output
vocabulary and schema identifiers. Source and derivative identities are recorded
in [source provenance](conformance/source-provenance.json).

## Build and verify

Use Python 3.11+, Git, GCC and a C++ compiler, CMake 3.27+, OCaml **5.5.1 bytecode**
and Lean **4.34.1**. Goose is pinned to
`9412b80f52d833c4697cffdbbf1f4eeb5195cd41`.

```sh
sh tools/build_goose.sh /absolute/path/to/goose
sh tools/build_ocaml.sh /absolute/path/to/ocaml-source /absolute/path/to/ocaml-install
export GOOSE_SOURCE=/absolute/path/to/goose
export OCAMLC=/absolute/path/to/ocaml-install/bin/ocamlc
export LEAN=/absolute/path/to/lean-4.34.1/bin/lean

make pins        # Verify pinned external sources and local extraction provenance
make test        # Compare all supported observations with Lean and OCaml
make smoke       # Exercise the complete timing pipeline on small fixtures
make audit       # Verify and run the external estate auditor
make acceptance  # All scaffold gates with a source-bound verification receipt
```

The comparison checkout is fetched at its exact commit into a temporary directory
when `LEAN_OCAML_SOURCE` is unset. For offline use, point `LEAN_OCAML_SOURCE` at
a clean checkout of the pinned Lean-OCaml revision. Builds and third-party
sources stay outside this repository. Existing supplied checkouts are verified
and never reset or modified.

`make benchmark` runs the full seven-family comparison with seven samples and
128 definitions per batch. `BENCHMARK_ARGS` can select sample counts, worker
limits and output location. Compiler setup and the hosted path are visible in
[CI](.github/workflows/conformance.yml).

## Implemented scope

The [reference](reference/checker.goose) supports numeric sorts, de Bruijn
variables, dependent Pis and lambdas, applications, typed lets, beta/zeta
reduction and transparent monomorphic definitions. It checks all constant
occurrences, capture-avoiding substitution, duplicate names and failed-insertion
state. Fresh batches use fresh arenas, environments and caches.

General universe expressions, inductives, recursors, quotients, opaque or
recursive declarations, eta, proof irrelevance and `.olean` import remain
outside this implementation. Eta and proof-irrelevance examples are explicit
registered differences from Lean in the conformance gate.

## Review surfaces

| File | Purpose |
| --- | --- |
| [Architecture](ARCHITECTURE.md) | Authority boundaries, planes and promotion requirements |
| [Estate manifest](ESTATE.toml) | Research/candidate identity and pinned governance |
| [Observation contract](schemas/definition-observations-v1.md) | Input DAG and evidence-only output schemas |
| [Dependency pins](conformance/dependencies.json) | Exact compiler/comparison revisions and archive hashes |
| [Source provenance](conformance/source-provenance.json) | Original and locally adapted Goose bytes |
| [Validation guide](docs/validation.md) | Gates, reproducibility and evidence interpretation |
| [Historical benchmark](docs/benchmark-baseline.md) | Prior measurements and their exact source identity |
| [Next obligations](docs/roadmap.md) | Concrete compatibility and performance work |
| [Language boundaries](LANGUAGE_BOUNDARIES.md) | Local ownership, external oracles and generated C |

The scaffold follows the pinned estate repository template v2. Its position is
`research / layer 3 / EXPLORE / candidate`, with Goose as canonical language and
`acceptance_authority = false`. A local layout pass establishes local conformance;
estate-wide registration and authority promotion are separate decisions.

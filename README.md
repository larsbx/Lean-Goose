# Lean-Goose: bounded Lean migration reference

Goose implementation of the bounded expression-checking fragment used by the
Lean kernel migration experiments. This repository owns the Goose reference;
the native Lean and OCaml bytecode comparison engines are pinned external
dependencies. The reference produces observations and has no declaration,
theorem, deployment or other admission authority.

The repository adopts **estate-repository-v3** with unrestricted implementation
languages and required **Lean and Quint formalization**. The required formal
scopes cover ordered definition transactions, preservation of complete stored
bindings, structural expression DAGs with binder scope, and capture-avoiding
lifting and substitution. Stored records retain
names, declared types, original values, and inferred types. The
[formalization document](docs/formalization.md) identifies the claims,
implementation mapping, required checks, and remaining correspondence work.
Execution status belongs to the source-bound receipts for the revision tested.

The reference is derived from
[Lean-OCaml PR #8](https://github.com/larsbx/Lean-OCaml/pull/8) at
`403dcca50d7e8f18954618eec72109f8cb1c6b61`. The local derivation applies the four
recorded presentation changes, then an exact reviewed diagnostic patch adding
bounded stored-binding traces. The v2 [source-provenance contract](conformance/source-provenance.json)
binds the original source, patch, preserved checking/parser function prefix,
and final local bytes.

## Build and verify

Use Python 3.11+, Git, GCC and a C++ compiler, CMake 3.27+, OCaml **5.5.1 bytecode**,
Lean **4.34.1**, and Quint **0.33.1**. The workflow uses Node **24.22.3**. Goose is
pinned to `9412b80f52d833c4697cffdbbf1f4eeb5195cd41`.

```sh
sh tools/build_goose.sh /absolute/path/to/goose
sh tools/build_ocaml.sh /absolute/path/to/ocaml-source /absolute/path/to/ocaml-install
export GOOSE_SOURCE=/absolute/path/to/goose
export OCAMLC=/absolute/path/to/ocaml-install/bin/ocamlc
export LEAN=/absolute/path/to/lean-4.34.1/bin/lean
npm --prefix formal/quint ci --ignore-scripts --no-audit --no-fund

make pins          # Verify external pins and local extraction provenance
make test          # Compare supported observations with Lean and OCaml
make formal-tests  # Exercise formal-runner acceptance and rejection controls
make formal        # Execute proofs, model checks, and finite runtime comparison
make smoke         # Exercise the complete timing pipeline on small fixtures
make audit         # Verify and run the external estate auditor
make acceptance    # Execute all required gates and write source-bound evidence
```

The comparison checkout is fetched at its exact commit into a temporary directory
when `LEAN_OCAML_SOURCE` is unset. For offline use, point `LEAN_OCAML_SOURCE` at
a clean checkout of the pinned Lean-OCaml revision. Compiler builds and comparison
sources stay outside this repository. The Quint dependency installation is
ignored by Git; its package lock is committed. Supplied checkouts are verified
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

The formal models cover smaller, stated subsets of the implementation. The
original transaction lane retains its 21 Lean obligations and 1,110 finite
cases. The stored-binding lane requires 29 additional Lean obligations,
16 Quint tests, and 2,954 finite cases spanning two names and sort levels zero
and one. Its gate compares complete model states and every processed snapshot,
then checks both native `--trace` and `--check` behavior.

The [expression-DAG lane](docs/expression-dag-scope.md) adds 30 required Lean
theorems and 21 Quint tests for all seven node kinds, topology refusal, immutable
decoded prefixes, structural height, and de Bruijn scope. Its finite profile
contains every topology-valid graph of one to three nodes over seven selected
leaves: 2,163 graphs, each probed natively at four binder depths. It also requires
an empty graph, 27 malformed-topology controls, and 17 named context and typing
controls. Every distinct native snapshot arena is replayed through both models.
The [substitution lane](docs/substitution.md) adds 32 required Lean theorems and
30 Quint tests for cutoff/index rules, scope preservation, lifting identities,
and capture avoidance beneath arbitrary nested lambdas. Both actual models
evaluate 2,546 requests. A separately generated diagnostic harness calls the
checker's actual `lift` and `substitute` functions, compares full result
expressions, and preserves every imported raw node and ID. Its 2,576 native
commands also exercise parser/resource refusals and ordinary checking controls.
The harness preserves the entire checker source except for renaming its main
entrypoint; the appended driver and generated source are separately identified.

All four Quint models run seeded, bounded invariant simulations and designated
negative controls. The DAG simulation has an eight-node arena cap; substitution
has a six-node cap. Both stutter at their bounds. Their replay inventories and
the unbounded Lean theorems have separate coverage meanings.

The opt-in [`--trace` contract](schemas/binding-trace-v1.md) exposes raw stored
type/value/inferred node IDs and the immutable node DAG after each processed
definition. The finite stored-binding profile decodes Sort/Const payloads and
checks preservation of the raw records and existing node payloads. The added DAG
lane covers structural payloads for applications, lambdas, Pis, typed lets, and
variables. Native scope is checked through observable completion or scope
refusal; the trace does not expose internal `free` or height metadata. General
correctness of Goose inference, substitution, normalization, caches, and the
implementation's refinement of these models remains unproved.

`make acceptance` retains the broader 964 ordered outcomes per engine, six
structural/resource controls, and seven-family benchmark smoke alongside all four
formal scopes. Large replay and native-comparison logs are preserved as gzip
files; [the reproduction notes](docs/formalization.md#reproduction-and-receipts)
explain how to inspect them. Required inventories describe what a successful run
must establish; they do not relabel an earlier receipt as a pass for new code.

## Review surfaces

| File | Purpose |
| --- | --- |
| [Architecture](ARCHITECTURE.md) | Authority boundaries, implementation, and promotion requirements |
| [Estate manifest](ESTATE.toml) | Research/candidate identity, v3 formal scope, and pinned governance |
| [Formalization scope](docs/formalization.md) | Lean claims, Quint checks, runtime mapping, and limits |
| [Observation contract](schemas/definition-observations-v1.md) | Input DAG and evidence-only output schemas |
| [Stored-binding trace](schemas/binding-trace-v1.md) | Bounded snapshots of stored records and immutable node payloads |
| [Expression-DAG scope](docs/expression-dag-scope.md) | Structural representation, binder scope, finite native probes, and limits |
| [DAG replay contract](schemas/expression-dag-replay-v1.md) | Canonical raw nodes, structural expression wires, and strict model observations |
| [Substitution scope](docs/substitution.md) | Lifting and substitution laws, actual-function comparison, and remaining refinement work |
| [Substitution replay contract](schemas/substitution-replay-v1.md) | Operation inputs, transformed-root observations, and native diagnostic boundary |
| [Dependency pins](conformance/dependencies.json) | Exact compiler/comparison revisions and archive hashes |
| [Source provenance](conformance/source-provenance.json) | Original and locally adapted Goose bytes |
| [Validation guide](docs/validation.md) | Gates, reproducibility, and evidence interpretation |
| [Historical benchmark](docs/benchmark-baseline.md) | Prior measurements and their exact source identity |
| [Next obligations](docs/roadmap.md) | Concrete formal, compatibility, and performance work |
| [Implementation inventory](LANGUAGE_BOUNDARIES.md) | Current languages, external comparisons, and generated C |

The estate position remains `research / layer 3 / EXPLORE / candidate`, with
`acceptance_authority = false` and `origin.decided_by = "proposed"`. This v3
adoption supplies scoped formal work and its execution path. Estate membership,
stage promotion, and a new accepting boundary remain explicit decisions.

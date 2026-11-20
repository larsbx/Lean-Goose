# Validation and reproduction

## Toolchains and pins

Goose, the comparison checkout, Lean, and OCaml are identified in
`conformance/dependencies.json`. External Git source pins are SHA-256 digests of
the deterministic, uncompressed output of `git archive --format=tar REVISION`.
The runner requires the exact revision, a clean tracked source tree, matching
archive bytes, and matching consumed-file hashes. A wrong or modified checkout
fails before comparison.

`conformance/source-provenance.json` identifies the upstream Goose source and
the local observation-only derivative. The original blob, source SHA-256,
explicit replacements, and local SHA-256 make the extraction reviewable.

The local proof lane uses Lean `leanprover/lean4:v4.34.1`, revision
`5045d0056413266e57c625dcd7c365b10e377c52`. Quint is pinned to
`@informalsystems/quint@0.33.1` with a committed npm lockfile. The workflow uses
Node `24.22.3`. Install the locked dependencies before the formal gate:

```sh
npm --prefix formal/quint ci --ignore-scripts --no-audit --no-fund
```

Goose emits standalone C with `-O2 -DGS_DEBUG=1`; GCC compiles the result with
`-O2`. Bounds checks remain enabled, with compiler-proven elimination, and
debug-defined overflow/range/tag checks remain active. Temporary generated C
and binary hashes are recorded. All local expression-checking rules originate
in the local Goose source.

## Gates

| Command | Evidence |
| --- | --- |
| `make pins` | External checkout and local source-provenance verification |
| `make test` | Full finite observation comparison against native Lean and OCaml |
| `make formal-tests` | Formal-runner acceptance and rejection controls |
| `make formal` | Lean proof replay and audit, Quint checks, and finite transaction comparison |
| `make smoke` | Small fresh three-engine benchmark execution |
| `make audit` | Pinned external estate v3 manifest audit |
| `make acceptance` | All required gates, logs, source manifest, and verification receipt |
| `make benchmark` | Optional full performance experiment with repeated samples |

The external estate audit checks declarations and file inventories. Actual
formal execution is a separate required gate. `make acceptance` executes both,
along with the existing conformance and smoke gates. The workflow invokes the
repository acceptance entrypoint for the source under review.

### Existing expression comparison

At 128 definitions per workload, the expression comparison covers 964 ordered
outcomes per engine across 16 fixtures: the committed typing corpus, definition
and failed-insertion state cases, annotation/erasure controls, shared-context
and capture cases, the two registered conversion differences, and seven
128-definition workloads. Six extra Goose parser/scope/resource controls must
exit with the designated diagnostic. These controls remain required alongside
the new formal scope.

### Formal transaction comparison

The formal gate checks the action model described in
[formalization.md](formalization.md). Its finite runtime inventory consists of
all **1,110 nonempty sequences of length at most three** over ten actions on two
names: two good definitions, two mismatches, four directed aliases, and two
scope failures. The input sequences are encoded as actual DAG files for the
native Goose executable.

For nonfatal traces, comparison checks ordered names and outcome categories,
success count, schema, and absence of admission authority. For fatal traces,
it requires the designated scope-failure exit and diagnostic, with no completed
definition-observation JSON. The runtime does not expose an environment list;
model-state equality and runtime-output agreement are distinct checks.

The scope document distinguishes these finite tests from the unbounded Lean
model theorems and Quint's seeded bounded exploration. Missing tool output,
unrecognized outcomes, or an arbitrary command failure cannot stand in for a
successful gate or a designated negative control.

### Timing smoke

The smoke run uses all seven families with eight definitions, one sample, and
one worker per engine. It exercises compilation, calibration, measurement, and
receipt writing in this checkout. The historical seven-sample study retains its
own source identity, and no speed threshold determines smoke success.

## Receipt meaning

The top-level receipt is `conformance/evidence/verification.json`. The formal
gate writes `conformance/evidence/formal/results.json`. Their source inventories,
logs, toolchain identities, outcomes, and before/after checks identify the
execution being reported. The formal receipt records model proof/check results
and the stated finite runtime comparison; it does not certify full implementation
refinement or estate-wide adoption.

A new attempt invalidates prior success before checking prerequisites. Command
failure, missing declared inputs, or relevant source changes fail verification.
Generated evidence remains under `conformance/evidence/` and is excluded from
its own source digest. Dependency installations and build outputs are excluded;
declared source, scope, implementation, profile, and gate inputs must remain
covered by the formal receipt's inventory.

Hosted CI is separately bound to its exact revision. Local and hosted outcomes
are recorded independently; a queued job is not successful evidence. An earlier
receipt remains evidence about its recorded inputs, even after new source is
published. The historical benchmark is never updated by changing its labels.

After an implementation or formal-scope change, run `make acceptance`. After a
performance change, also retain the full workload/configuration results, input
hashes, failures, timing boundaries, and sample ranges from a fresh benchmark.

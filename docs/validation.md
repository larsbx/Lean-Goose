# Validation and reproduction

## Toolchains and pins

Goose, the comparison checkout, Lean and OCaml are identified in
`conformance/dependencies.json`. External Git source pins are SHA-256 digests of
the deterministic, uncompressed output of `git archive --format=tar REVISION`.
The runner requires the exact revision, a clean tracked source tree, matching
archive bytes and matching consumed-file hashes. A wrong or modified checkout
fails before comparison.

`conformance/source-provenance.json` identifies the upstream Goose source and
the local observation-only derivative. The original blob, source SHA-256,
explicit replacements and local SHA-256 make the extraction reviewable.

Goose emits standalone C with `-O2 -DGS_DEBUG=1`; GCC compiles the result with
`-O2`. Bounds checks remain enabled, with compiler-proven elimination, and
debug-defined overflow/range/tag checks remain active. Temporary generated C
and binary hashes are recorded. All local expression-checking rules originate
in the local Goose source.

## Gates

| Command | Evidence |
| --- | --- |
| `make pins` | External checkout and local source-provenance verification |
| `make test` | Full finite observation comparison against Lean and OCaml |
| `make smoke` | Small fresh three-engine benchmark execution |
| `make audit` | Pinned external estate layout audit |
| `make acceptance` | All scaffold gates, logs, source manifest and verification receipt |
| `make benchmark` | Optional full performance experiment with repeated samples |

At 128 definitions per workload, the finite comparison covers 964 ordered
outcomes per engine across 16 fixtures: the committed typing corpus, definition
and failed-insertion state cases, annotation/erasure controls, shared-context
and capture cases, the two registered conversion differences, and seven
128-definition workloads. Six extra Goose parser/scope/resource controls must
exit with the designated diagnostic. The test checks observations, not a
mathematical refinement theorem.

The smoke run uses all seven families with eight definitions, one sample and
one worker per engine. Its purpose is to exercise compilation, calibration,
measurement and receipt writing in this checkout. It is not a replacement for
the historical seven-sample study, and no speed threshold determines success.

## Receipt meaning

The verification receipt identifies source bytes before and after execution,
commands, toolchains, logs and outcomes. Any failed command or source change
fails verification. Generated evidence stays in `conformance/evidence/`; it is
excluded from its own source digest. Source inputs, tooling, schema and policy
files remain included.

`passed` records a successful test observation. It cannot be used as a theorem,
declaration, authorization or deployment verdict. Hosted CI is separately bound
to its exact revision; a local pass is not a hosted pass, and a queued job is
not successful evidence.

After an implementation change, run full comparison and the scaffold gates.
After a performance change, retain all workload/configuration results, input
hashes, failures, timing boundaries and sample ranges. Do not replace older
measurements with new source labels.

# Historical benchmark baseline

The initial performance evidence was collected in **Lean-OCaml**, before this
standalone scaffold. It belongs to implementation commit
`9a6c54f961ddb6b8f6a9b0020a6265cde913fdba`; its report and receipts were published
at `403dcca50d7e8f18954618eec72109f8cb1c6b61` in
[PR #8](https://github.com/larsbx/Lean-OCaml/pull/8).

These are historical observations, not a fresh full measurement of Lean-Goose.
The extraction preserves the checking algorithm and adapts output vocabulary
and schemas. The scaffold performs fresh conformance and smoke checks under its
own source identity.

## Recorded medians

Milliseconds per batch of 128 definitions, median of seven sample averages.
Goose and Lean used one native worker; the displayed OCaml lane is bytecode with
one worker. The upstream report retains the 1/2/4/8-worker results and ranges.

| Workload | Lean native | Goose AOT | OCaml bytecode |
| --- | ---: | ---: | ---: |
| `wide` | 2.936 | 0.022 | 0.544 |
| `chain` | 0.926 | 0.025 | 0.914 |
| `identities` | 0.555 | 0.023 | 0.379 |
| `distinct_trees` | 2.892 | 0.236 | 25.915 |
| `unshared_trees` | 2.658 | 2.662 | 44.652 |
| `dependent_terms` | 2.816 | 0.420 | 24.101 |
| `alias_diamonds` | 1.126 | 0.119 | 10.922 |

The six substantial median improvements justify further investigation. The
unshared-tree medians differ by approximately 0.14 percent and their ranges
overlap; that lane establishes no useful advantage over Lean.

The experiment uses synthetic supported-fragment workloads. Goose's cache and
fuel accounting and sequential insertion differ from OCaml's planned concurrent
batches. Parsing, compilation, warm-up and validation are untimed; Goose's fresh
arena import is timed. These results combine implementation and runtime effects
and do not establish whole-project or full-Lean-kernel performance.

## Immutable evidence

- [Full report](https://github.com/larsbx/Lean-OCaml/blob/403dcca50d7e8f18954618eec72109f8cb1c6b61/docs/goose-benchmark.md)
- [All 294 samples, 42 configurations and toolchain identities](https://github.com/larsbx/Lean-OCaml/blob/403dcca50d7e8f18954618eec72109f8cb1c6b61/conformance/evidence/goose-comparison/results.json)
- [Source identity verification](https://github.com/larsbx/Lean-OCaml/blob/403dcca50d7e8f18954618eec72109f8cb1c6b61/conformance/evidence/goose-comparison/source-correspondence.json)
- [Differential observations](https://github.com/larsbx/Lean-OCaml/blob/403dcca50d7e8f18954618eec72109f8cb1c6b61/conformance/evidence/goose-comparison/fixtures/results.json)

Run `make benchmark` to create a fresh complete measurement for a particular
Lean-Goose revision. Keep that result separate from this baseline.

# Definition observation contracts v1

## Runtime input: `lean-ocaml-benchmark-dag-v1`

Input is UTF-8 text ending with LF. The first line is the exact schema name.
Remaining rows are tab separated. Node IDs start at zero and are contiguous;
every child reference must point to an earlier node. All node rows precede
definition rows. Names contain nonempty ASCII letters, digits or underscores.

| Row/tag | Fields after the tag | Meaning |
| --- | --- | --- |
| `n ID s` | `level` | Numeric sort |
| `n ID v` | `index` | de Bruijn variable |
| `n ID c` | `name` | Transparent constant |
| `n ID a` | `function argument` | Application |
| `n ID l` | `domain body` | Lambda, with one binder in body |
| `n ID p` | `domain codomain` | Dependent Pi, with one binder in codomain |
| `n ID t` | `type value body` | Typed let, with one binder in body |
| `d` | `name type-node value-node` | Ordered definition observation |

Each encoded node is constructed once; sharing in the DAG is preserved. The
parser bounds sort numerals to 128, numeric fields to 1,000,000, input nodes to
1,000,000 and definitions to 4,096. A semantic comparison may use smaller
inventories. These are experiment resource bounds.

## Ordered output: `lean-goose.definition-observations.v1`

`checker --check FILE` emits one JSON object with:

| Field | Contract |
| --- | --- |
| `schema` | `lean-goose.definition-observations.v1` |
| `engine` | `goose-aot` |
| `status` | `checked` |
| `outcomes` | Ordered `{name, outcome}` records, one per definition |
| `success_observations` | Count of `observed_success` results |
| `acceptance_authority` | Always `false` |

The success observation is `observed_success`. Designated semantic refusals
are `Unknown_constant`, `Duplicate_definition`, `Expected_sort`,
`Expected_function` and `Type_mismatch`. A refused definition does not enter the
environment; subsequent definitions still observe the prior bindings.

Parser, scope, depth and resource failures are nonzero process exits rather than
semantic success/refusal observations. They cannot satisfy a registered semantic
expectation. Unknown or malformed output also fails the comparison.

## Timing output: `lean-goose.benchmark-observation.v1`

`checker FILE 1 ITERATIONS` supports one Goose worker and 1 through 100,000
iterations. Each batch starts fresh, checks its full definition inventory, and
undergoes untimed result verification. One untimed warm-up and an ill-typed-sort
refusal control precede measurements.

The JSON result includes the schema ID, engine, `status: passed`, workers,
iterations, definition count, positive elapsed nanoseconds, per-batch time,
validated-batch count, refusal-control count and `acceptance_authority: false`.
`passed` means the benchmark's checks completed; it is not a domain verdict.

## External normalization and registered differences

The pinned Lean/OCaml observer contract uses a historical success label. The
adapter translates only that explicit label and its count field into this
repository's observation vocabulary. Semantic refusal categories retain their
registered mapping. The adapter cannot turn a parser/resource/internal failure
into a successful observation.

Lean reports success on the two named eta and proof-irrelevance specimens while
both bounded references report `Type_mismatch`. Only these specific specimens
permit that directional difference. Broader conversion or resource equivalence
is not claimed.

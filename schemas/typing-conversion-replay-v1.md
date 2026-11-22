# Typing/conversion replay v1

This JSONL protocol is shared by `TypingConversionReplay.lean` and
`formal/quint/typing_replay.py`. It observes the executable semantic models;
it is not a declaration admission interface or the native checker resource
contract. All native comparison cases additionally use the existing
`lean-ocaml-benchmark-dag-v1` format.

## Request

Each nonempty line is exactly one JSON object with keys `nodes`, `definitions`,
and `fuel`. Duplicate keys, extra/missing keys, booleans in numeric fields,
negative/fractional/exponent/nonfinite numerals, malformed JSON, empty streams
and blank lines are refused. A complete valid line may be evaluated before a
later line fails; stdout from a failing helper invocation is never accepted as
a completed replay by the gate.

| Field | Meaning |
| --- | --- |
| `nodes` | 1–128 canonical raw nodes, each `[tag,a,b,c,nameCodes]`. Tags 0–6 mean sort, variable, constant, application, lambda, Pi and typed let. All child IDs must point to earlier nodes. |
| `definitions` | 1–64 entries `[nameCodes,typeId,valueId]` in checking order. Both selectors address `nodes`. |
| `fuel` | Natural number 0–256; evaluator recursion-depth budget, distinct from native work fuel. |

Names are nonempty vectors of ASCII letters, digits and underscore. Sort and
variable payloads are natural numbers; their unused fields are zero and names
empty. Constants have zero `a/b/c` fields. Binary constructors have zero `c`;
all compound nodes have empty names. Lets have three meaningful child IDs.
These are the same canonical payload conventions as the existing model wires.

Before structural decoding, both helpers compute each raw node's expanded
expression-wire size by a topological pass: two for sort/variable, two plus
name length for constants, and one plus the sum of child sizes for compound
nodes. The sum over all nodes must not exceed **65,536 tokens**. This diagnostic
envelope is not a theorem about native resource consumption.

## Result

Each successfully evaluated request produces one complete JSON line:

```json
{
  "schema": "lean-goose.typing-conversion-model.v1",
  "steps": [],
  "halted": false,
  "acceptance_authority": false
}
```

The empty `steps` above only illustrates the envelope; a valid nonempty request
has at least one processed snapshot. Each step has exactly `name`, `outcome`
and `bindings`. Names remain ASCII-code vectors. Each binding has exactly
`name`, `type`, `value` and `inferred`. The expression fields use prefix vectors:

| Constructor | Expression vector |
| --- | --- |
| Sort | `[0,level]` |
| Variable | `[1,index]` |
| Constant | `[2,nameLength,...nameCodes]` |
| Application, lambda, Pi | `[tag,...leftExpression,...rightExpression]` |
| Typed let | `[6,...typeExpression,...valueExpression,...bodyExpression]` |

The type/value fields retain original structural syntax; inferred is the
normalized inferred type. Successful steps append exactly one full binding;
all refusals retain the complete prior list. Earlier records remain unchanged.

| Outcome | Meaning |
| --- | --- |
| 0 | `observed_success` |
| 1 | `Invalid_scope`; stops the model trace |
| 2 | `Unknown_constant` |
| 3 | `Duplicate_definition` |
| 4 | `Expected_sort` |
| 5 | `Expected_function` |
| 6 | `Type_mismatch` |
| 9 | `ModelFuelExhausted`; stops the model trace and is never a native comparison expectation |

`halted` is true exactly when the last step has outcome 1 or 9. Later input
definitions are unprocessed after that step. A code-9 JSON result is an explicit
model observation, not native code-7 resource failure or a semantic success.

## Execution and identity

Lean reads a request, validates its complete line, decodes with the existing
DAG model, evaluates the new semantic model, and serializes its result. Quint
executes an independent continuation machine using the existing Quint DAG and
substitution infrastructure. Its numeric internal wire echoes the request's
position and every raw node/name/definition/budget field, then length-frames
the observation. The Python helper validates exact identity, order, cardinality,
numeric types and framing before emitting JSON. Python does not decide typing,
reduction, conversion, or successful inferred fields.

Quint's evaluator has a separate **2,048-transition cap per evaluator call**.
Its internal exhaustion code 10 makes the helper fail with no emitted results;
it is not a public semantic outcome. Four requests are grouped per Quint REPL
command. The gate retains complete ordered requests, source hashes and outputs.

Malformed requests produce exit 2 with prefix
`invalid typing/conversion replay input:` in Lean, or exit 1 with prefix
`Quint typing replay failed:` in the Quint helper. Runtime failures and missing,
extra, reordered or malformed output fail the correspondence gate.

## Native and external projections

The Goose `--trace` comparison independently decodes raw nodes and checks every
processed full binding. It also requires exact original input IDs, earlier
binding IDs, immutable node prefixes, and process status. Fatal scope must
produce a halted trace but no completed `--check` receipt. Native snapshots
retain the existing trace bound of 4,194,304 bytes; decoded observation expansion
is limited to 1,000,000 tokens per expression and 2,000,000 per table.

Native Lean and OCaml expose ordered definition outcomes, not compound binding
records. Their 44-fixture comparison therefore establishes finite success and
refusal agreement only. It must not be described as stored-field observation
from those external engines or general kernel compatibility.

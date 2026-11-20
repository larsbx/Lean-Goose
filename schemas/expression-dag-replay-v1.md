# Expression DAG replay contract v1

This contract connects the Lean and Quint expression/DAG models to finite graph
cases and to immutable node tables emitted by the existing native
[`--trace` contract](binding-trace-v1.md). It specifies structural decoding,
height, and binder scope. It does not specify definition checking or grant
acceptance authority.

The document's version is not an additional JSON field. Requests and responses
have exactly the fields below. The native input and trace schemas are unchanged.

## Request stream

Input is a nonempty JSONL stream: one JSON object per nonempty line. Each object
has exactly two fields:

| Field | Type and meaning |
| --- | --- |
| `nodes` | Ordered list of raw nodes; list position is the node ID |
| `depths` | Ordered list of natural-number ambient binder depths to query for every decoded node |

Both lists may be empty. Query depths may be repeated or unsorted; their order
and multiplicity are preserved. The native comparison profile uses depths
`[0,1,2,3]`; the replay contract accepts arbitrary natural-number depth lists.

A natural number is a nonnegative JSON integer. Booleans, negative numbers,
floating-point numbers, and nonfinite JSON constants do not satisfy that type.
Duplicate object keys, missing fields, extra fields, and blank input lines are
malformed input.

### Raw node shape

Every node is an array of exactly five elements:

```text
[tag, a, b, c, nameCodes]
```

The first four fields are natural numbers. `nameCodes` is a list of natural
numbers. The following table gives the complete constructor inventory:

| Numeric tag | Native tag | Constructor | `a` | `b` | `c` | `nameCodes` |
| --- | --- | --- | --- | --- | --- | --- |
| `0` | `s` | Sort | Level | `0` | `0` | `[]` |
| `1` | `v` | Variable | de Bruijn index | `0` | `0` | `[]` |
| `2` | `c` | Constant | `0` | `0` | `0` | Nonempty ASCII identifier bytes |
| `3` | `a` | Application | Function ID | Argument ID | `0` | `[]` |
| `4` | `l` | Lambda | Domain ID | Body ID | `0` | `[]` |
| `5` | `p` | Pi | Domain ID | Codomain ID | `0` | `[]` |
| `6` | `t` | Let | Type ID | Value ID | Body ID | `[]` |

Constant identifiers contain only ASCII letters, digits, or underscore: byte
ranges `65..90`, `97..122`, `48..57`, and byte `95`. All other name lists must be
empty. Unused numeric fields must be zero. Unknown tags and noncanonical unused
fields are malformed input. The models treat a constant's name vector opaquely;
the ASCII restriction belongs to this replay/native boundary.

Only the meaningful child fields in the table are edges. Every child of node
`i` must have an ID strictly less than `i`. A self reference, forward reference,
or escaping ID causes **topology refusal**. A cycle necessarily violates the
same earlier-child requirement. Topology refusal is a model result, distinct
from malformed JSON or a noncanonical node record.

## Response stream

A successful invocation returns one JSON object per request, in the original
order, with exactly these six fields:

| Field | Type and meaning |
| --- | --- |
| `decoded` | Boolean indicating whether the entire node table decoded |
| `expressions` | Structural prefix-token vector for each node, in node-ID order |
| `heights` | Natural-number structural height for each node |
| `loose` | Natural-number minimum ambient binder depth required by each node |
| `scoped` | Boolean matrix, indexed first by node ID and then by requested depth position |
| `acceptance_authority` | Exactly the JSON Boolean `false` |

For a decoded table of `n` nodes and `m` query depths, the four outer arrays
have length `n`, and every `scoped` row has length `m`. No array is reordered or
deduplicated. JSON object key order is immaterial.

Topology refusal is atomic at this interface:

```json
{"decoded":false,"expressions":[],"heights":[],"loose":[],"scoped":[],"acceptance_authority":false}
```

The response does not fabricate an expression for the invalid node or expose a
partially decoded table. An empty table is valid and has the same empty arrays
with `decoded: true`.

A malformed request, evaluator error, missing executable, timeout, or malformed
evaluator response must cause a nonzero helper exit. It must not be translated
to topology refusal. The caller must reject an unsuccessful invocation rather
than consume any partial results it may have received. The Quint helper validates
all requests and all returned batches before emitting any observation.

### Lossless structural prefix tokens

The structural wire expands shared children by their content. Constructor arity
determines expression boundaries; constant names additionally carry their byte
count. In the table below, `++` means list concatenation and `E(x)` is the
structural encoding of child expression `x`.

| Expression | Token vector |
| --- | --- |
| Sort at level `n` | `[0,n]` |
| Variable at index `i` | `[1,i]` |
| Constant with name bytes `name` | `[2,length(name)] ++ name` |
| Application of `f` to `x` | `[3] ++ E(f) ++ E(x)` |
| Lambda with domain `d` and body `b` | `[4] ++ E(d) ++ E(b)` |
| Pi with domain `d` and codomain `b` | `[5] ++ E(d) ++ E(b)` |
| Let with type `t`, value `v`, and body `b` | `[6] ++ E(t) ++ E(v) ++ E(b)` |

This wire preserves constructor order, numeric payloads, and every constant
name byte. It is a structural expression representation. The original request
retains node IDs and sharing; equal expression vectors do not imply equal raw
DAG layouts.

### Height and scope

Let `pred(n) = max(n - 1, 0)`. The height `H` and required binder depth `L` are:

| Constructor | `H` | `L` |
| --- | --- | --- |
| Sort or constant | `1` | `0` |
| Variable `i` | `1` | `i + 1` |
| Application `a b` | `1 + max(H(a), H(b))` | `max(L(a), L(b))` |
| Lambda or Pi `a b` | `1 + max(H(a), H(b))` | `max(L(a), pred(L(b)))` |
| Let `t v b` | `1 + max(H(t), H(v), H(b))` | `max(L(t), L(v), pred(L(b)))` |

The binder applies to the body or codomain. It does not bind variables in a
lambda/Pi domain, let type, or let value. For node `i` and query position `j`,
`scoped[i][j]` is `loose[i] <= depths[j]`. Closedness is the query at depth zero.
Being in scope does not establish that an expression is well typed or that a
constant is defined.

For example, the same open subtree can be used under different numbers of
binders:

```json
{"nodes":[[0,0,0,0,[]],[1,1,0,0,[]],[4,0,1,0,[]],[4,0,2,0,[]]],"depths":[0,1,2,3]}
```

The exact result is:

```json
{
  "decoded": true,
  "expressions": [[0,0],[1,1],[4,0,0,1,1],[4,0,0,4,0,0,1,1]],
  "heights": [1,1,2,3],
  "loose": [0,2,1,0],
  "scoped": [[true,true,true,true],[false,false,true,true],[false,true,true,true],[true,true,true,true]],
  "acceptance_authority": false
}
```

## Snapshot extension

If a later valid node table contains an earlier table as an exact raw prefix,
decoding the later table preserves every earlier expression, height, and loose
requirement at its original ID. Scope rows are also preserved when the same
depth list is queried. A consumer must compare the raw fields as well as the
decoded projection: structural equality alone can hide a changed sharing layout.

If a later suffix has invalid topology, the later whole-table response is the
atomic refusal object. The interface does not return the earlier prefix as a
successful partial result.

## Quint execution and evidence

[`dag_replay.py`](../formal/quint/dag_replay.py) validates canonical input, emits
only data literals to the actual pinned Quint TypeScript evaluator, and decodes
length-framed numeric results from
[`ExpressionDag.qnt`](../formal/quint/ExpressionDag.qnt). One evaluator process
handles each helper invocation's requests, grouped into commands of at most
32 cases. Each returned case echoes its ordinal, complete raw node table, and
exact depth list. The
adapter rejects missing, extra, duplicated, changed, or reordered identities.

The owned gate groups the complete ordered inventory into sequential helper
invocations of at most 256 requests. Each invocation starts a fresh evaluator;
within it, the 32-case command grouping above still applies. Lean evaluates the
complete inventory once, and every Quint chunk is compared with the exact
corresponding Lean slice. Chunking changes process resource use, not the case
inventory or the comparison fields. The receipt retains the whole compressed
input plus each chunk's starting index, count, stdin digest, command name, and
the associated command log digest.

The evaluator's stdout is captured in a regular temporary file; its complete
JSON values are parsed independently of pretty-print line breaks. The Python
adapter contains no expression decoder, height calculation, binder-scope
calculation, or topology decision. Source-bound gate receipts record the actual
execution results; this contract alone establishes no passed check.

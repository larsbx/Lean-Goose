# Lifting and substitution replay contract v1

This contract defines model replay and the separate native diagnostic harness
for structural lifting and capture-avoiding single-variable substitution.
It uses the raw nodes and structural token encoding of the
[expression-DAG contract](expression-dag-replay-v1.md). The ordinary checker
`--check` and [binding-trace](binding-trace-v1.md) protocols remain unchanged.
Every result has `acceptance_authority: false`.

The document version is not an additional replay JSON field. The
[scope specification](../docs/substitution.md) describes the required proofs,
exploration, finite inventories, and limitations.

## Model request stream

Input is a nonempty JSONL stream containing one nonempty JSON object per line.
Each request has exactly six fields:

| Field | Type and meaning |
| --- | --- |
| `nodes` | Nonempty ordered raw-node list; position is the original node ID |
| `operation` | Integer `0` for lifting or `1` for substitution |
| `root` | Natural-number ID selecting the expression to transform |
| `parameter` | Lift amount for operation `0`; replacement raw-node ID for operation `1` |
| `cutoff` | Natural-number de Bruijn cutoff at the selected root |
| `depths` | Ordered list of natural-number ambient binder depths for querying the transformed root |

`root < nodes.length` is required. For substitution,
`parameter < nodes.length` is also required. A replacement may occur after
the selected root in the raw table, may duplicate another node's payload,
and may itself be a compound expression. The selected root need not be the
last node. Neither the root nor the replacement must be closed or well typed.

A natural is a nonnegative JSON integer. Boolean, floating-point, exponent,
negative, and nonfinite values are rejected; JSON `-0` denotes integer zero.
Duplicate keys, missing/extra fields, unknown operations, invalid selectors,
an empty node list, blank lines, and malformed JSON are process errors.
`depths` may be empty, repeated, or unsorted. Its order and multiplicity must
be preserved. The general model contract imposes no native numeric cutoff
bound; the finite native profile uses depths `[0,1,2,3,4,5,6]`.

### Canonical raw nodes

Every raw node is an array of exactly five fields:

```text
[tag, a, b, c, nameCodes]
```

The first four fields are natural numbers. The final field is a list of
natural-number ASCII identifier bytes.

| Tag | Native tag | Constructor | `a` | `b` | `c` | `nameCodes` |
| --- | --- | --- | --- | --- | --- | --- |
| `0` | `s` | Sort | Level | `0` | `0` | `[]` |
| `1` | `v` | Variable | Index | `0` | `0` | `[]` |
| `2` | `c` | Constant | `0` | `0` | `0` | Nonempty name bytes |
| `3` | `a` | Application | Function ID | Argument ID | `0` | `[]` |
| `4` | `l` | Lambda | Domain ID | Body ID | `0` | `[]` |
| `5` | `p` | Pi | Domain ID | Codomain ID | `0` | `[]` |
| `6` | `t` | Let | Type ID | Value ID | Body ID | `[]` |

Constant names contain only ASCII letters, digits, or underscore: byte ranges
`65..90`, `97..122`, `48..57`, or byte `95`. All other name lists are empty.
Unused numeric fields are zero. Unknown tags or noncanonical fields are
process errors.

Every meaningful child ID must be strictly smaller than the containing node's
ID. A self, forward, missing, or cyclic reference gives a **topology refusal**.
The entire table is checked, including nodes unused by the selected root or
replacement. A bad unused suffix cannot be ignored. This model result is
distinct from malformed framing or invalid operation arguments.

## Transformation rules

For a variable index `i`, amount `a`, cutoff `c`, and replacement `r`:

```text
lift(a,c,Var i) = Var i                 when i < c
lift(a,c,Var i) = Var (i+a)             when i >= c

substitute(r,c,Var i) = Var i           when i < c
substitute(r,c,Var i) = lift(c,0,r)     when i = c
substitute(r,c,Var i) = Var (i-1)       when i > c
```

Sorts and constants retain their exact payloads. Both operations recurse using
the following cutoffs:

| Constructor | Child cutoffs |
| --- | --- |
| Application | Function `c`, argument `c` |
| Lambda | Domain `c`, body `c+1` |
| Pi | Domain `c`, codomain `c+1` |
| Let | Type `c`, value `c`, body `c+1` |

Each shared occurrence is evaluated in its own binder context. Substitution
inserts the replacement lifted by the current cutoff and decreases indices
above the removed slot. It does not evaluate beta/zeta reductions, infer a
type, resolve constant names, or insert a definition.

## Model response stream

A successful invocation returns one LF-terminated JSON object per request,
in the same order, with exactly these six fields:

| Field | Meaning |
| --- | --- |
| `decoded` | Boolean indicating whether the entire raw DAG decoded |
| `expressions` | One structural token vector for the transformed root, or `[]` on topology refusal |
| `heights` | One positive natural-number structural height, or `[]` |
| `loose` | One natural-number minimum ambient binder requirement, or `[]` |
| `scoped` | One ordered Boolean row for the requested depths, or `[]` |
| `acceptance_authority` | Exactly JSON Boolean `false` |

For a valid request, all four outer arrays have length **one**, including
when the raw DAG has many nodes. The scope row has length `depths.length`.
For malformed topology the exact semantic result is:

```json
{"decoded":false,"expressions":[],"heights":[],"loose":[],"scoped":[],"acceptance_authority":false}
```

No partially decoded table or partially transformed root is exposed. Empty
nodes are malformed input under this contract, so there is no successful
empty-table result.

### Structural tokens and metadata

Let `E` denote structural encoding and `++` list concatenation:

| Expression | Token vector |
| --- | --- |
| Sort `n` | `[0,n]` |
| Variable `i` | `[1,i]` |
| Constant `name` | `[2,length(name)] ++ name` |
| Application `f x` | `[3] ++ E(f) ++ E(x)` |
| Lambda `d b` | `[4] ++ E(d) ++ E(b)` |
| Pi `d b` | `[5] ++ E(d) ++ E(b)` |
| Let `t v b` | `[6] ++ E(t) ++ E(v) ++ E(b)` |

Constructor arity and explicit name length delimit the wire. Shared raw nodes
are expanded by content without assigning model result IDs. Every tag,
literal, name byte, and child order must be preserved or transformed according
to the operation rules.

Write `pred(n) = max(n-1,0)`. Height `H` and required depth `D` are:

| Constructor | Height | Required ambient depth |
| --- | --- | --- |
| Sort or constant | `1` | `0` |
| Variable `i` | `1` | `i+1` |
| Application `f x` | `1+max(H(f),H(x))` | `max(D(f),D(x))` |
| Lambda/Pi `d b` | `1+max(H(d),H(b))` | `max(D(d),pred(D(b)))` |
| Let `t v b` | `1+max(H(t),H(v),H(b))` | `max(D(t),D(v),pred(D(b)))` |

For each requested depth `d`, the scope answer is `D(result) <= d`.
`D(result) = 0` means scope-closed, independently of constant existence or
type correctness. Metadata describes the transformed expression, not the
original root and not the number of native allocations.

### Capture example

The request substitutes open `Var 0` for the free slot under one lambda:

```json
{"nodes":[[0,0,0,0,[]],[1,0,0,0,[]],[1,1,0,0,[]],[4,0,2,0,[]]],"operation":1,"root":3,"parameter":1,"cutoff":0,"depths":[0,1,2]}
```

The exact result is:

```json
{"decoded":true,"expressions":[[4,0,0,1,1]],"heights":[2],"loose":[1],"scoped":[[false,true,true]],"acceptance_authority":false}
```

The body cutoff is one, so the replacement becomes `Var 1`. The deliberately
wrong wire `[4,0,0,1,0]` would capture it and falsely make the result closed.
The required Quint negative witness preserves the request and changes only
the observed expression and loose requirement in this manner.

### Process failures and framing

Malformed input, an evaluator error, missing executable, timeout, or malformed
evaluator output must yield a nonzero helper exit. None may become a topology
refusal. Callers must discard all outputs of an unsuccessful invocation,
including any already emitted prefix. The Lean helper streams successful
requests and uses exit code `2` with diagnostic prefix
`invalid substitution replay input:` for invalid input. The Quint helper
validates the whole input and all returned batches before emitting output;
its invalid-input/evaluator failure path uses exit code `1` and prefix
`Quint substitution replay failed:`.

[`substitution_replay.py`](../formal/quint/substitution_replay.py) invokes the
actual pinned Quint TypeScript evaluator, loading module `Substitution`.
It writes data literals only and groups at most 32 requests per REPL command.
Each evaluator result echoes a numeric identity in this order:

```text
ordinal, nodeCount,
  each node: tag,a,b,c,nameLength,nameBytes...,
operation, root, parameter, cutoff, depthCount, depths...
```

That identity is followed by `decodedBit,authorityBit,resultCount` and, for
each result, `expressionLength,expressionTokens...,height,loose,scopeCount,
scopeBits...`. A successful result count is one; a refused result count is
zero. Booleans on this internal numeric wire use exact integers `0` or `1`.

The adapter rejects changed, missing, duplicated, reordered, additional,
truncated, or nonintegral data, including across command boundaries. It
captures stdout in a regular temporary file and parses complete JSON values
independently of pretty-print line breaks. It performs no topology,
transformation, height, loose-variable, or scope calculation in Python.

The gate invokes fresh helpers sequentially for at most 128 requests each,
compares each chunk with the corresponding Lean slice, and retains the full
ordered input and chunk identities. The six-node Quint simulation cap does
not restrict replay. The replay algorithm's context table is bounded by the
actual input's node count, not by an arbitrary iteration count or cutoff
value. Operational failure still fails the invocation.

## Native diagnostic harness

The native interface belongs to a generated diagnostic executable, not a new
mode added to `reference/checker.goose`:

```text
SUBSTITUTION_HARNESS --lift FIXTURE ROOT AMOUNT CUTOFF [OPERATION_FUEL]
SUBSTITUTION_HARNESS --substitute FIXTURE ROOT REPLACEMENT_ID CUTOFF [OPERATION_FUEL]
```

The fixture uses the existing tab-separated `lean-ocaml-benchmark-dag-v1`
format: contiguous node IDs, native tag characters from the table above,
constructor payloads, and a final LF. It must contain exactly one sentinel
definition row, with four tab-separated fields `d`, `transformation`, `0`,
`0`. The sentinel satisfies the inherited parser's definition inventory;
the driver does not check or insert it. The environment remains empty.

The driver imports the raw table using the original `import_nodes`, sets the
operation fuel after import, and calls the actual `lift` or `substitute`
at recursion depth one. An import failure is therefore distinct from a
transformation fuel failure. Open roots and open replacements are allowed.

### Native success and operation failure

A completed native operation emits exactly one bounded LF-terminated JSON
object with these fields:

| Field | Required value or meaning |
| --- | --- |
| `schema` | `"lean-goose.substitution-trace.v1"` |
| `engine` | `"goose-aot"` |
| `status` | `"transformed"` or `"halted"` |
| `operation` | `"lift"` or `"substitute"` |
| `root`, `parameter`, `cutoff` | Exact original numeric arguments |
| `fuel_budget` | Initial operation budget after normal import |
| `result` | Actual returned raw node ID on success; `null` on operation error |
| `error` | `0` on success; designated native error code on halt |
| `snapshot` | Raw arena and empty binding list, as specified below |
| `acceptance_authority` | Exactly `false` |

`snapshot` has exactly `name`, `outcome`, `nodes`, and `bindings`.
`name` is `"transformation"`; `outcome` is `"observed_success"` or the
designated error name; `bindings` is `[]`. Every node is an object with
exactly `tag`, `a`, `b`, `c`, and `name`, using native string tags and an ASCII
name string. The original node table remains an exact prefix, including all
unused inputs and original IDs. Derived nodes may follow it.

A successful process exits `0`, has empty stderr, and returns an in-range
node ID. The adapter walks that actual root and requires exact agreement
with the jointly computed model expression wire. It does not require a
particular derived node count or layout. Named identity controls additionally
require the actual original result or replacement ID.

An operation resource halt exits `2`. The designated cases are error `7`
(`Limit_exceeded`) or error `8` (`Height_limit`), with exact stderr
`goose bounded checker: ERROR_NAME` followed by LF. The trace has
`status: "halted"`, `result: null`, and the corresponding error/snapshot
outcome. No sentinel return ID is exposed as a model result. Any partial
derived arena is diagnostic data; the original raw prefix must still match.

Parser refusals exit `3` and emit no stdout. Malformed topology specifically
requires `goose benchmark parser: node reference must precede its use`
followed by LF. Import resource refusals and diagnostic-envelope refusals
exit `2` with no stdout. The latter use the inherited
`goose binding trace:` diagnostic prefix. The gate requires each registered
control's exact diagnostic; a different failure does not satisfy it.

### Bounds and comparison limits

The native parser accepts natural-number fields and CLI arguments in
`0..1,000,000`, with sort levels restricted to `0..128`. The driver defaults
to operation fuel `10,000,000` when the optional argument is absent; an
explicit fuel argument follows the parser's `1,000,000` maximum. The original
checker retains height/recursion-depth limit `128` and allocation ceiling
`2,000,000`. The diagnostic envelope is narrower: at most `4,096` imported
and final raw nodes, and `4,194,304` bytes each for fixture input and complete
serialized output, including its final LF. Output is buffered before print,
so an envelope refusal cannot expose a partial JSON object.

The comparison adapter additionally bounds total input/native-arena structural
expansion at `262,144` tokens, the result wire at `262,144` tokens, and each
model JSON line at `4,194,304` bytes. Each native process has a 15-second
timeout. These are execution/evidence bounds, not arithmetic assumptions in
the Lean operation definitions or a promise that every bounded raw graph is
well typed.

The snapshot intentionally omits native `height`, `free`, caches, remaining
fuel, and contexts. Native comparison checks the actual structural result
and unchanged input prefix. Lean and Quint independently compare the result
metadata and scope fields. This is not direct observation of native cached
metadata, exact allocation/fuel equivalence, or universal implementation
refinement.

### Exact source derivation and receipts

The [harness generator](../tools/substitution_harness.py) requires checker
SHA-256
`0de9dfe21a2e95fd0468fd9365ff8e73a18a22e91f457dd4e16209bf740f0e0a`
and matching [source provenance](../conformance/source-provenance.json).
It renames the unique checker entrypoint `main` to `original_main`, appends
the owned driver after a fixed separator, and verifies exact reconstruction
and reverse renaming. All other checker bytes remain identical. Generated
source is created exclusively in a new nonsymlink file outside the repository.

The required build uses the pinned external Goose compiler with
`-O2 -DGS_DEBUG=1 --standalone`, then GCC with `-O2 -lm -pthread`.
Runtime checks must be enabled in the generated C. The
`lean-goose.substitution-harness.v1` provenance record carries checker,
driver, and generated-source identities; the gate adds generated C and
native executable digests. Tool versions, executable digests, source
manifest, and external dependency verification belong to the enclosing
formal receipt.

The gate retains compressed model inputs, malformed/positive contract inputs,
actual model logs, exact counterexample ITF, generated harness source, and a
compressed native log containing every fixture, fixture digest, command,
timeout, stdout, stderr, and exit status. Reproduction and claim limits are
specified in the [scope document](../docs/substitution.md). Neither this
contract nor its required inventory alone asserts a passed acceptance run.

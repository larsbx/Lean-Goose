# Stored-binding diagnostic trace v1

`checker --trace FILE` reads the existing
[`lean-ocaml-benchmark-dag-v1`](definition-observations-v1.md) input and checks
definitions in their input order in a fresh state. It exposes the stored binding
records and immutable node payloads after each processed definition. The trace
is a bounded diagnostic observation with no acceptance authority.

This is an opt-in output contract. `--check` retains its existing
`lean-goose.definition-observations.v1` contract, including no completed receipt
on a fatal process exit. Benchmark mode retains its existing timing contract;
it does not allocate or serialize diagnostic snapshots.

## JSON envelope: `lean-goose.binding-trace.v1`

Within the trace bounds, the command emits exactly one JSON object followed by
LF. JSON object key order is not significant. The envelope has these fields:

| Field | Contract |
| --- | --- |
| `schema` | Exactly `lean-goose.binding-trace.v1` |
| `engine` | Exactly `goose-aot` |
| `status` | `traced` after all definitions finish with success or designated semantic refusal; `halted` after a processed fatal scope, height, or checker-resource result |
| `steps` | Ordered snapshots for the processed prefix of the input definitions, including the final fatal definition when `status` is `halted` |
| `success_observations` | Length of the stored environment after the last processed definition; equivalently the number of `observed_success` steps |
| `acceptance_authority` | Always the JSON boolean `false` |

A step has exactly these fields:

| Field | Contract |
| --- | --- |
| `name` | Input definition name |
| `outcome` | Existing `error_name` result from that invocation of `check_definition` |
| `bindings` | Complete stored environment immediately after that invocation, in insertion order |
| `nodes` | Complete immutable payload table of the current node arena immediately after that invocation |

The success label is `observed_success`. Designated semantic refusal labels are
`Unknown_constant`, `Duplicate_definition`, `Expected_sort`, `Expected_function`
and `Type_mismatch`. These refusals leave the binding environment unchanged and
permit the next definition to run. They may still allocate nodes during
checking, so equality of environments does not imply equality of arena lengths.

The diagnostic renderer does not run inference, normalization, substitution, or
validation. It serializes each step into the bounded output buffer immediately
after checking, before processing the next definition. It does not retain aliases
to mutable state for later rendering. Existing checking, parser, and cache
functions are unchanged.

## Stored bindings and raw node IDs

Each `bindings` entry has exactly four fields:

| Field | Contract |
| --- | --- |
| `name` | Stored binding name, a nonempty ASCII letter/digit/underscore string |
| `type` | Raw node ID stored in `Binding.ty`: the definition's declared type |
| `value` | Raw node ID stored in `Binding.value`: the definition's original value |
| `inferred` | Raw node ID stored in `Binding.inferred`: the normalized type inferred by the checker for the value |

All three IDs are nonnegative JSON integers indexing that step's `nodes` array.
The type and value IDs are the actual stored input IDs, not reconstructed or
normalized replacements. The inferred ID is the actual checker result, not a
fresh inference performed for diagnostics. In particular, a stored constant
alias retains its constant expression as its value; the trace does not replace
that expression with its target's value.

Successful insertion appends a binding. Earlier binding records remain present
with their original names and IDs. A trace consumer can compare the complete
records between successive snapshots and independently decode their structural
payloads. Such a finite comparison is evidence about the observed execution,
not a general refinement proof of the checker.

## Immutable node table

Array position is the node ID. Every node in the current arena is emitted once
per step, including unused input nodes and nodes allocated while checking.
Shared children are represented by their IDs and are not recursively expanded.
Original input IDs are retained, and derived nodes are appended. Nodes already
present retain their immutable payloads in later snapshots.

Each node has exactly `tag`, `a`, `b`, `c`, and `name`. All numeric fields are JSON
integers containing the raw stored fields. The interpretation depends on `tag`:

| `tag` | `a` | `b` | `c` | `name` |
| --- | --- | --- | --- | --- |
| `s` | Sort level | Unused | Unused | Unused |
| `v` | de Bruijn index | Unused | Unused | Unused |
| `c` | Unused | Unused | Unused | Constant name |
| `a` | Function node ID | Argument node ID | Unused | Unused |
| `l` | Domain node ID | Body node ID | Unused | Unused |
| `p` | Domain node ID | Codomain node ID | Unused | Unused |
| `t` | Type node ID | Value node ID | Body node ID | Unused |

Meaningful child IDs point to earlier array entries. Unused fields are still
exported as their raw values, normally numeric zero or the empty string. They
must not be interpreted as additional edges. The parser's ASCII name restriction
means all emitted names are valid JSON strings without escaping. No additional
node tags or fields are introduced by this schema.

The table deliberately omits `height`, `free`, `normal`, node `inferred`, and
`validated`. These are derived metadata and mutable caches. The binding field
named `inferred` is a stored node ID and remains part of the contract. The trace
does not claim cache-state, context-stack, or fuel-counter correspondence.

## Fatal diagnostics and process status

When `check_definition` returns `Invalid_scope`, `Height_limit`, or
`Limit_exceeded`, the command includes that definition's final snapshot, emits
the JSON object with `status: halted`, writes the existing
`goose bounded checker: <outcome>` diagnostic to stderr, and exits with code 2.
Later definitions are not run. Earlier successful bindings remain visible, and
the failed definition is not inserted.

This halted JSON is diagnostic data from an interrupted execution. It is not a
completed `--check` observation receipt and cannot satisfy a semantic
success/refusal expectation. A caller must inspect both process status and
schema/status, rather than treating any JSON on stdout as successful checking.

| Situation | Exit code | Stdout | Stderr |
| --- | --- | --- | --- |
| All definitions processed within the trace bounds | 0 | One `traced` JSON object | Empty |
| Fatal scope/height/checker-resource result after a definition is processed, with trace bounds still satisfied | 2 | One `halted` JSON object, including the fatal step | Existing `goose bounded checker:` diagnostic |
| Node import fails before any definition is processed | 2 | Empty | Existing `goose bounded checker:` diagnostic |
| Trace envelope or serializer limit is exceeded | 2 | Empty | Distinct `goose binding trace:` diagnostic |
| Malformed input within the trace input-byte bound | 3 | Empty | Existing `goose benchmark parser:` diagnostic |

An impossible internal serialization tag also uses the distinct trace diagnostic
and exits with code 2 without JSON. The existing refused-definition environment
count guard remains active; an internal guard failure is not a trace result.

## Trace-only resource bounds

| Bound | Value | Check point |
| --- | --- | --- |
| Input text | 4,194,304 bytes | After reading the file, before parsing |
| Input nodes | 4,096 | After parsing, before importing into checker state |
| Definitions | 64 | After parsing, before importing into checker state |
| Derived arena size | 4,096 nodes, including imported nodes | After every `check_definition`, before serializing its snapshot |
| Serialized output | 4,194,304 bytes, including the final LF | Before every append to the single output buffer |

These limits apply only to `--trace`. The existing parser, checker, and benchmark
limits continue to govern the other modes. The input-byte check bounds parsing
work for diagnostics; it occurs after the existing file-reading operation. The
derived-arena check is a diagnostic envelope check after checking a definition,
not a change to the checker's node-allocation limit.

The entire JSON object is buffered, with one byte reserved for the terminating
LF. If any trace bound is exceeded, buffered snapshots are discarded by the
process exit and no partial JSON is printed. Trace-bound failure takes precedence
over producing a halted snapshot if the same definition also returned a fatal
checker result. Large or highly shared expressions do not cause recursive output
expansion: each snapshot serializes the bounded raw DAG table.

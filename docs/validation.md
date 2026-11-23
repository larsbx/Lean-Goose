# Validation and reproduction

## Toolchains and pins

Goose, the comparison checkout, Lean, and OCaml are identified in
`conformance/dependencies.json`. External Git source pins are SHA-256 digests of
the deterministic, uncompressed output of `git archive --format=tar REVISION`.
The runner requires the exact revision, a clean tracked source tree, matching
archive bytes, and matching consumed-file hashes. A wrong or modified checkout
fails before comparison.

`conformance/source-provenance.json` v2 identifies the upstream Goose source,
the four original presentation replacements, and the reviewed diagnostic patch
in `reference/binding-trace.patch`. The runner applies the patch with exact
contexts, offsets, paths, and hashes, then compares the reconstructed source
with the owned checker bytes. It also verifies that all 18,034 bytes of the
original checking and parser function prefix remain unchanged. The extension
adds opt-in tracing and main dispatch; it is no longer a presentation-only port.

The local proof lane uses Lean `leanprover/lean4:v4.34.1`, revision
`5045d0056413266e57c625dcd7c365b10e377c52`. Quint is pinned to
`@informalsystems/quint@0.33.1` with a committed npm lockfile. The workflow uses
Node `24.22.3`. Install the locked dependencies before the formal gate:

Formal Lean compilation, axiom audits, and replay pass `--threads=1`, fixing the
worker count independently of the host CPU inventory. The actual flag is
recorded with the toolchain and each command. This scheduling choice does not
change proof obligations or the axiom audit.

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
| `make formal` | All six Lean proof inventories and axiom audits, independent Quint models, finite transaction/binding/DAG/substitution/typing comparisons, and native controls |
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
definition-observation JSON. This original `--check` lane does not expose an
environment list; model-state equality and runtime-output agreement are
distinct checks.

### Stored-binding comparison

The additional required lane runs all **2,954 nonempty sequences of length one
through three** over fourteen actions on two names and two sort levels. Both
executed models must agree on all type, value, and inferred-type payloads in the
final environment and every intermediate snapshot. The profile has 2,032
completed traces, 922 designated scope halts, and 7,546 snapshots.

Each input runs through both native `--trace` and `--check`. The trace adapter
decodes actual node IDs into the profile's Sort/Const payloads, compares every
full binding with the model, checks exact retention of earlier raw binding IDs
and immutable node payloads, and checks that successful insertions retain the
declared input type and value IDs. The same input must still satisfy the existing
`--check` output or fatal-exit contract. This comparison is finite; it does not
establish general expression refinement, compiler correctness, or cache-state
correspondence.

`tools/binding_trace_controls.py` adds 26 required native checks of all seven
node tags, semantic refusals, processed scope/height/fuel failures, import and
parser failures, and trace resource limits. Fatal trace JSON is diagnostic data
from an interrupted execution, not a completed checking receipt. No partial
JSON may escape when a trace envelope limit fails.

The stored-binding Lean model has 29 required axiom-free theorems, alongside the
original 21. Quint has 16 additional deterministic tests and a separate seeded
1,000-trace run of at most 40 transitions. Its designated negative control must
produce the exact two-state witness in which a refused definition illegally
changes an existing value from `[0,0]` to `[0,999]`. An arbitrary command failure
does not satisfy that control.

Large replay and native comparison logs are losslessly compressed:
`stored-lean-replay.log.gz`, `stored-quint-replay.log.gz`, and
`stored-native-comparison.jsonl.gz` under `conformance/evidence/formal/`.
The native comparison records the actual stdout, stderr, and exit code for both
modes on every input. Read a JSONL log with:

```python
import gzip
import json

with gzip.open("conformance/evidence/formal/stored-native-comparison.jsonl.gz", "rt") as stream:
    for line in stream:
        execution = json.loads(line)
        # execution["model"] and execution["native"]["--trace"] identify this case.
```

The scope document distinguishes these finite tests from the unbounded Lean
model theorems and Quint's seeded bounded exploration. Missing tool output,
unrecognized outcomes, or an arbitrary command failure cannot stand in for a
successful gate or a designated negative control.

### Expression-DAG and scope comparison

The [DAG lane](expression-dag-scope.md) requires 30 additional Lean theorems,
21 Quint tests, seeded exploration with an eight-node arena cap, and a strict
two-state negative witness for an incorrect binder decrement. Its common
[JSONL replay contract](../schemas/expression-dag-replay-v1.md) preserves all raw
node payloads, actual constant-name bytes, structural expression wires, heights,
minimum binder requirements, and scope answers.

Both actual models evaluate 2,208 initial requests: 2,163 valid graphs, one empty
graph, 27 malformed graphs, and 17 named controls. The valid graphs each produce
four native scope probes. Malformed and named controls also run `--check`, for
8,740 native commands in this lane. Each distinct native arena request is then
replayed through Lean and Quint, with every observed snapshot linked back to its
request. Comparison checks original decoded prefixes, raw binding identities,
immutable node prefixes, and scope completion/refusal. The native trace omits
internal `free` and height metadata; equality of those fields is between the
models, while native scope is observed through checker behavior.

The receipt records the actual number of unique arenas and snapshots, complete
compressed model and native logs, and source identities. A parser rejection is
separate from a semantic scope halt. Shared-DAG expansion has explicit
serialization bounds; hitting one fails the gate rather than dropping cases.
Quint replay uses sequential fresh invocations of at most 256 requests, bounding
REPL source/history growth. Exact chunk offsets, counts, and input hashes link
every command to the complete ordered inventory. Lean evaluates the same entire
inventory, and each Quint chunk is compared with the corresponding Lean slice.
The repository runner allows 2,400 seconds for the expanded six-scope formal gate and
records that timeout in its receipt. Individual formal commands retain their
300-second limit and native probes retain their 15-second limit. This changes
the orchestration budget, not the checker resource bounds or required cases.
The hosted workflow allows 60 minutes for toolchain setup and the complete
acceptance sequence.

### Lifting and substitution comparison

The [substitution lane](substitution.md) requires 32 additional Lean theorems
with empty transitive axiom sets and a complete namespace audit. Quint executes
30 deterministic tests and 1,000 seeded samples of at most eight transitions,
with a six-node arena cap and stuttering at the bound. The exact negative
witness inserts an unlifted free variable beneath a lambda and captures it.

Lean and actual Quint evaluate 2,546 operation requests. Each Quint invocation
contains at most 128 requests, internally grouped into commands of at most 32;
the complete ordered Lean result is compared against every corresponding chunk.
The native diagnostic harness executes the checker's actual functions. For
2,540 transformed results, the result ID must point into the returned arena,
the entire expression wire must match, and every imported node must retain its
original raw ID and payload. Six topology cases require exact parser refusal.

Fourteen additional native controls separate parser, import, operation resource,
and diagnostic-envelope failures. Eight ordinary definition controls execute
both `--trace` and `--check`, covering beta/zeta capture and malformed scope.
This lane requires 2,576 native process executions. The native `free` and height
metadata is not exposed; model metadata agreement is not relabeled as direct
native metadata observation.

The generated harness changes only the unique checker main identifier and
appends the driver. Exact reconstruction, checker and driver hashes, generated
source/C/binary hashes, and enabled runtime checks are recorded. Complete native
fixtures, commands, stdout, stderr, exits, and predictions are retained. Each
actual replay helper must also reject 22 malformed requests and agree on three
fixed positive contract cases. Earlier receipts do not verify the new scope.

### Typing and conversion comparison

The [typing/conversion lane](typing-conversion.md) requires 32 new Lean
successful-execution soundness and stored-field theorems, 26 deterministic Quint
tests, 1,000 seeded samples of at most eight transitions (four processed
snapshots), and the exact corrupted-inferred-field negative witness. Both
actual models evaluate all 48 authored requests. Native Goose executes each in
both trace and check modes, for 96 commands and 66 processed snapshots from
67 input definitions; one definition is intentionally suppressed after a fatal
scope outcome.

The standalone conformance gate adds 44 common-fragment fixtures and 59 ordered
outcomes per engine, retaining the previous 964-outcome inventory separately.
These external Lean/OCaml drivers do not expose stored fields. Four native-only
scope/competing-error-priority cases remain explicit in the formal comparison.
No new semantic disagreement is permitted in the common fragment. The complete
local Python comparison dependency set is included in standalone source hashes.

The actual replay helpers each reject 24 malformed requests and report model
budget exhaustion separately. The diagnostic envelope, Quint continuation cap,
input/output identities and complete compressed logs are described in the
[replay contract](../schemas/typing-conversion-replay-v1.md). None of these
budgets is identified with native resource accounting. The theorem and finite
execution scopes retain their different meanings.

### Semantic-environment preservation

The [sixth lane](semantic-environment.md) requires 37 Lean obligations and
24 Quint tests, 1,000 samples of at most eight transitions with a four-snapshot
cap, and the exact old-value corruption witness. Its independent semantic
certificates and lookup-preserving weakening are model theorems. Quint checks
component evaluation equations and frozen predecessor histories finitely.

Twelve additional histories run through the unchanged actual Lean and Quint
typing replay helpers and both native Goose modes: 62 definitions, 61 processed
snapshots and 24 native commands. Ten common-reference histories add 52 ordered
outcomes per engine, recorded separately from the older 964 and 59 outcomes.
The native diagnostic interface exposes full records, not semantic proof
certificates. Inferred-field scope, valid binder contexts, typed reduction and
universal native refinement remain explicit next obligations.

### Timing smoke

The smoke run uses all seven families with eight definitions, one sample, and
one worker per engine. It exercises compilation, calibration, measurement, and
receipt writing in this checkout. The historical seven-sample study retains its
own source identity, and no speed threshold determines smoke success.

## Receipt meaning

The top-level receipt is `conformance/evidence/verification.json`. The formal
gate writes `conformance/evidence/formal/results.json`. Their source inventories,
logs, toolchain identities, outcomes, and before/after checks identify the
execution being reported. The v6 formal receipt records all six scopes,
including its `stored_bindings`, `expression_dag`, `substitution`,
`typing_conversion`, and `semantic_environment` sections,
and the stated finite runtime comparisons; it
does not certify full implementation
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

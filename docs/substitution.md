# Lifting and capture-avoiding substitution

This scope adds structural lifting and single-variable substitution to the
seven-constructor expression model. It requires unbounded Lean statements,
independent Quint computation, and a finite comparison with the actual
`lift` and `substitute` functions in the owned Goose checker. The ordered-name,
stored-binding, and expression-DAG scopes remain required. Every observation
retains `acceptance_authority: false`.

The [replay and native harness contract](../schemas/substitution-replay-v1.md)
defines the exact request, result, diagnostic, and refusal formats. The
[owned gate](../tools/check_substitution.py) defines the required executions.
Counts in this document specify coverage; only a completed receipt for the
matching source establishes that those executions passed.

## Operation semantics

Both operations use natural-number de Bruijn indices. Let `L(a,c,e)` mean
lifting expression `e` by amount `a` at cutoff `c`, and let `S(r,c,e)` mean
substituting replacement `r` at cutoff `c`.

| Variable case | Lifting | Substitution |
| --- | --- | --- |
| `i < c` | `Var i` | `Var i` |
| `i = c` | `Var (i + a)` | `L(c,0,r)` |
| `i > c` | `Var (i + a)` | `Var (i - 1)` |

Sort levels and constant names are unchanged. Application applies the operation
to both children at the same cutoff. Lambda and Pi apply it to the domain at
`c` and the body or codomain at `c + 1`. Let applies it to the type and value
at `c`, and to the body at `c + 1`. The replacement is lifted when inserted;
the surrounding binders must not capture its free variables. These rules are
implemented structurally in
[`Substitution.lean`](../formal/lean/Substitution.lean) and independently in
[`Substitution.qnt`](../formal/quint/Substitution.qnt).

For example, substitute open `Var 0` into the free slot of
`Lambda (Sort 0) (Var 1)` at cutoff zero. The lambda body is visited at cutoff
one, so the result is `Lambda (Sort 0) (Var 1)`: the inserted variable remains
free. Inserting unlifted `Var 0` would instead bind it to that lambda and
change the expression's minimum required ambient depth from one to zero.
The required negative control exercises exactly this mistake.

### Structural metadata

The result carries structural height and `loose`, the minimum ambient binder
depth required to put every variable in scope. It inherits the definitions in
the [expression-DAG scope](expression-dag-scope.md): leaves have height one,
compound height is one plus the maximum child height, and `Var i` has
`loose = i + 1`. Lambda and Pi decrement only the body's loose requirement;
let decrements only the body's requirement. Decrements saturate at zero.
`Scoped d e` holds exactly when `loose e <= d`.

These properties do not resolve constant names or establish that an expression
has a type. The transformed root may be open, and its replacement may be open.
The structural result expands shared children by content. Raw input IDs and
the native returned root ID are retained separately; structural equality does
not require equal allocation counts or a unique sharing layout.

## Lean statements and audit

Namespace `GooseSubstitution` imports the existing `GooseExpressionDag`
expression, decoder, scope relation, height, and loose-variable definitions.
Its operations recurse over arbitrary finite structural expressions, with
natural-number amounts, cutoffs, and indices. They do not inherit the native
integer, height, fuel, or allocation limits.

The 32 required theorem names are declared in the manifest and checked by
[`SubstitutionAudit.lean`](../formal/lean/SubstitutionAudit.lean):

| Group | Required theorem names, after `GooseSubstitution.` |
| --- | --- |
| Lift variable and binder equations | `lift_var_below`, `lift_var_at_or_above`, `lift_lambda`, `lift_pi`, `lift_let` |
| Lift identities and structural bounds | `lift_zero`, `lift_add`, `lift_preserves_height`, `lift_fixed_of_scoped`, `lift_closed`, `lift_scope`, `lift_loose_bound` |
| Substitution variable and binder equations | `substitute_var_below`, `substitute_var_equal`, `substitute_var_above`, `substitute_lambda`, `substitute_pi`, `substitute_let` |
| Substitution fixed points and scope | `substitute_fixed_of_scoped`, `substitute_closed`, `substitute_scope`, `substitute_closed_top` |
| Substitution/lift identities | `substitute_lift_one`, `substitute_lift_one_top`, `substitute_variable_after_lift` |
| One-binder capture avoidance | `lambda_substitution_avoids_capture`, `pi_substitution_avoids_capture`, `let_substitution_avoids_capture` |
| Arbitrarily nested capture avoidance | `nested_lambda_substitution_avoids_capture`, `nested_lambda_free_variable_stays_free` |
| Observation boundary | `refused_observation_is_empty`, `observe_has_no_authority` |

The general scope statement is:

```text
Scoped (n + c + 1) e and Scoped n r
  imply Scoped (n + c) (S(r,c,e)).
```

At `n = c = 0`, a term scoped at depth one and a closed replacement produce
a closed result. The fixed-point statements say that an expression already
scoped below the cutoff is unchanged. Lifting preserves structural height,
preserves scope with an additional `a` ambient binders, and increases the
loose requirement by at most `a`.

The audited identities include:

```text
L(0,c,e) = e
L(b,c,L(a,c,e)) = L(a+b,c,e)
S(r,c,L(1,c,e)) = e
S(Var 0,c,L(1,c+1,e)) = e
```

The nested-lambda family quantifies over any natural nesting depth `k`.
Substituting at the slot `c + k` under those binders inserts
`L(c+k,0,r)`. For replacement `Var i`, the inserted index is `i + c + k`,
so it remains outside all `k` surrounding binders.

Every required theorem must have an empty transitive axiom closure. The audit
also visits every declaration in the namespace, including generated support;
only the separately reported support allowlist containing `propext` is
permitted there. A missing theorem, a non-theorem declaration substituted for
an obligation, or an unapproved axiom fails the audit. The gate records the
compiled model hash and actual namespace/declaration counts.

These are proofs about the Lean model. They do not prove that arbitrary
compiled Goose executions refine the model. The
[Lean replay adapter](../formal/lean/SubstitutionReplay.lean) evaluates the
model on the shared finite inputs; that computation and the native comparison
are separately required evidence.

## Quint computation and exploration

The Quint implementation builds a table indexed by raw node and relative
binder depth. For an `N`-node input, node `i` has offsets `0..N-1-i`.
Every child `j < i` has a longer row, so both the current offset and the
body's incremented offset are available. This bound is derived from the
input topology and covers every possible binder path. Numeric index and
cutoff magnitudes do not increase the number of table contexts. There is no
fuel-exhaustion branch returning a fabricated expression.

Lift plans carry a structural wire and a Boolean mask marking eligible
variable-index tokens. Applying an amount changes only those tokens. Tags,
sort levels, constant-name lengths, and name bytes remain unchanged. A plan
for the replacement at cutoff zero is reused at substitution sites, applying
the site's current cutoff as the lift amount. All plan construction,
transformation, constructor reconstruction, metadata, and topology decisions
execute in Quint.

The required `Substitution.safety` invariant checks the exact observation,
absent authority, successful result shape, positive height, nonnegative loose
requirement, and fixed points below the cutoff. It also checks lift height
preservation and scope bounds, substitution height and scope bounds, and
closedness for a top-level substitution with a closed replacement.

### Required bounded run

The gate uses Quint **0.33.1**, its **TypeScript backend**, seed **20261120**,
**1,000 samples**, and at most **eight transitions per sample**. The simulation
starts with one `Sort 0` and grows to **six nodes**, then stutters. Each
extension can choose any of the seven tags, payloads/amounts/cutoffs in
`0..3`, every earlier child ID, either operation, and every current root or
replacement ID. Constants use the names `n0` through `n3`.

This is sampled bounded exploration. It is neither exhaustive enumeration
of all bounded executions nor an unbounded Quint proof. The general replay
does not impose the simulator's six-node cap on supplied inputs.

The 30 deterministic controls must execute once each:

| Controls | Behavior exercised |
| --- | --- |
| `liftZeroTest`, `liftBelowCutoffTest`, `liftAtCutoffTest`, `liftAboveCutoffTest` | Zero lift and the three variable/cutoff cases |
| `sortPayloadUnchangedTest`, `constantNameUnchangedTest` | Opaque leaf payload preservation |
| `applicationBothChildrenTest`, `lambdaDomainAndBodyTest`, `piDomainAndBodyTest`, `letValueAndBodyTest` | Correct child positions and binder cutoffs |
| `substituteBelowCutoffTest`, `substituteAtCutoffTest`, `substituteAboveCutoffTest`, `substituteApplicationTest` | Variable replacement/decrement and application traversal |
| `lambdaAvoidsCaptureTest`, `piAvoidsCaptureTest`, `letAvoidsCaptureTest`, `nestedBindersAvoidCaptureTest` | Lifted replacement under one or multiple binders |
| `replacementOwnBinderTest`, `sharedNodeDifferentDepthsTest` | A replacement's own binder and shared nodes in distinct contexts |
| `selectedRootNotLastTest`, `hugeCutoffDoesNotBoundTraversalTest` | Original root selection and input-derived traversal size |
| `closedSubstitutionResultTest`, `emptyDepthQueriesTest` | Result scope and an empty query list |
| `selfReferenceRefusalTest`, `forwardReferenceRefusalTest`, `unusedInvalidSuffixRefusalTest` | Atomic whole-table topology refusal |
| `authorityPreservedTest`, `triangularRowsCoverAllContextsTest`, `simulationBoundStuttersTest` | Authority, table dimensions, and the simulator cap |

### Designated wrong-capture control

`unsafeInit` sets the exact request from the capture example in the
[contract](../schemas/substitution-replay-v1.md#capture-example). Its correct
observation is wire `[4,0,0,1,1]`, height `2`, and loose requirement `1`.
`unsafeStep` preserves the request but inserts the unlifted replacement,
producing wire `[4,0,0,1,0]`, height `2`, and loose requirement `0`.
Both states retain `decoded: true` and `acceptance_authority: false`.

The gate requires exit code `1`, the designated invariant-violation diagnostic,
and exactly two ITF states with those request and observation values. The ITF
header must identify this model and a violation, its variable inventory must
be exactly `q` and `observed`, and state indices must be zero and one. Duplicate
keys, nonfinite values, or extra state fields are refused. A parser error,
missing executable, timeout, or unrelated failure cannot satisfy this control.

## Finite actual-function correspondence

[`substitution_profile.py`](../tools/substitution_profile.py) generates the
required inventory. Its leaf alphabet is `Sort 0`, `Sort 1`, `Var 0` through
`Var 3`, and `Const missing`. A node at position `i` can additionally use all
three binary constructors with any earlier child pair, or let with any
earlier child triple.

The profile includes every one- and two-node graph over this alphabet:
`7 + 7 * 11 = 84` graphs. Each graph's last node is the operation root.
There are nine lifts per graph, combining amounts `0..2` and cutoffs `0..2`.
There are 21 substitutions per graph, combining each of the seven leaves
with cutoffs `0..2`; the replacement is appended as a new raw node, preserving
the original graph and root ID even when its payload duplicates an old node.

| Inventory | Required count |
| --- | --- |
| Generated lifts | `84 * 9 = 756` |
| Generated substitutions | `84 * 21 = 1,764` |
| Total generated operations | `2,520` |
| Named controls | `20` |
| Malformed-topology controls | `6` |
| Complete Lean/Quint/native profile | `2,546` |
| Successful native transformation results | `2,540` |

All profile requests use scope depths `[0,1,2,3,4,5,6]`. Named controls cover
nested lambda/Pi/let binders, shared variable nodes at different depths,
compound open replacements, exact name payloads, zero lifts, high cutoffs,
and original IDs for unchanged results or a direct replacement. Malformed
controls exercise self, forward, and missing references with both operations.
Malformed topology produces an atomic model refusal and a native parser
refusal; it is never counted as a transformed expression.

Lean evaluates the complete ordered inventory. Quint evaluates the same
inventory through sequential helper invocations of at most **128 requests**,
with **32 cases per internal REPL command**. Every result field must match the
corresponding Lean result exactly. The helper checks the ordinal, complete
raw table, operation, root, parameter, cutoff, and depth list echoed by the
actual evaluator. Python contains no alternative lift or substitution engine.

### Native harness derivation

[`substitution_harness.py`](../tools/substitution_harness.py) constructs a
temporary source from the exact owned checker and
[`substitution-driver.goose`](../reference/substitution-driver.goose).
The sole change to checker bytes is renaming its unique `main` identifier to
`original_main`; the diagnostic driver is then appended. The generator
checks an exact reverse transformation and byte-for-byte reconstruction.
It creates a new file outside the repository and refuses existing files,
symlinks, or a destination inside the repository.

The checker SHA-256 is
`0de9dfe21a2e95fd0468fd9365ff8e73a18a22e91f457dd4e16209bf740f0e0a`,
matching [source provenance v2](../conformance/source-provenance.json).
All parser, import, transformation, metadata, allocation, and resource
functions are retained. The driver calls the real `lift` or `substitute`
and serializes the returned root ID plus the complete raw arena; it performs
no substitute computation, type inference, or definition insertion.

The native comparison verifies the exact input argument IDs, every original
raw node as an unchanged prefix, and every token of the expression reached
from the returned root. It allows different derived allocation layouts
when their returned structural expression agrees. Selected controls also
require the exact existing root or replacement ID to be returned.

The native trace omits internal `height`, `free`, normalization/inference
caches, and remaining fuel. Consequently, height, loose, and scope agree
between the two actual models, while native correspondence directly checks
the transformed structural payload and original raw prefix. This lane does
not claim direct observation or universal correctness of cached metadata.

### Additional refusal and ordinary-check controls

Fourteen diagnostic controls require exact process outcomes and diagnostics:
six parser/argument controls; zero operation fuel; allocation fuel exhaustion;
lift-index overflow; overflow while lifting an inserted replacement;
result-height overflow; import-height overflow; and input/derived node-envelope
overflow. Operation resource failures expose `result: null` in a halted
snapshot. Parser, import, and diagnostic-envelope refusals emit no result.
These cases are separate from mathematical model outputs.

Eight ordinary definition cases run through both existing `--trace` and
`--check` modes: application beta, nested-let capture, open lambda/Pi domains,
open let type/value/body, and an open beta-capture example. Their fixed
observations exercise use of the operations during ordinary checking.
They add 16 native executions. The complete new lane therefore requires
**2,546 + 14 + 16 = 2,576 native process executions**.

The replay contract also requires **22 malformed input cases through each
helper**, giving 44 rejection executions. Three positive requests exercise
empty depths, repeated/unsorted depths, and a cutoff of `1,000,000,000`;
each helper evaluates all three. These contract controls are separate from
the 2,546-case native profile and do not expand the native numeric bounds.

## Toolchains, bounds, and evidence

The [formal gate](../tools/check_formal.py) pins Lean **4.34.1** at revision
`5045d0056413266e57c625dcd7c365b10e377c52`, with `--threads=1`, Quint
**0.33.1**, and Node **24.22.3**. The
[dependency contract](../conformance/dependencies.json) pins the external
Goose source at `9412b80f52d833c4697cffdbbf1f4eeb5195cd41` and the comparison
repository at `403dcca50d7e8f18954618eec72109f8cb1c6b61`, including archive
and consumed-file hashes. Their checkouts remain external and unmodified.

The harness uses Goose `-O2 -DGS_DEBUG=1 --standalone` and GCC
`-O2 -lm -pthread`. The gate checks that generated C contains enabled runtime
checks and records driver, generated source, generated C, and binary hashes.
The outer formal receipt records actual tool identities and dependency checks.

The comparison profile bounds raw arenas at **4,096 nodes**, expanded wire
tokens at **262,144**, and model JSON lines at **4 MiB**. The native driver
inherits **4 MiB** input/output envelopes and the **4,096-node** diagnostic
bound, while its underlying checker retains height/depth **128**, allocation
ceiling **2,000,000**, and default operation fuel **10,000,000**. Native CLI
naturals, including an explicit optional fuel value, are bounded by
**1,000,000**; the omitted fuel argument uses the larger default. Sort levels
are bounded by **128** at the native parser. These operational bounds do not
restrict the mathematical Lean statements.

Run `make formal-tests` for the repository's gate/adapter rejection controls,
`make formal` for all declared formal lanes, and `make acceptance` for the
complete required source-bound acceptance gate. The substitution lane is
required within the full formal gate; it is not a replacement for existing
checks. Environment/toolchain setup is described in
[validation](validation.md).

The receipt retains the compressed complete model input, every Quint chunk's
starting index/count/stdin digest, command logs, the exact negative ITF trace,
the generated harness source, and the compressed native comparison log with
fixtures, arguments, process output, and timeouts. Native commands have a
15-second timeout; formal subprocesses and each Quint helper have a
300-second timeout. A timeout or missing result fails the lane.
Local receipt success and hosted CI status remain distinct facts about the
exact source identities they record.

## Remaining boundary

This scope proves structural operation laws in Lean and requires the stated
independent execution evidence. It does not prove general implementation
refinement, parser correctness, compiler correctness, native cache validity,
resource-accounting equivalence, typing preservation, normalization,
definitional equality, confluence, or full Lean compatibility. The ordinary
beta/zeta cases are finite regressions, not a metatheory of reduction or typing.

Subsequent obligations must connect these structural laws to typing and
conversion, state invariants for the actual checker, and a precise refinement
relation with its allocation and refusal behavior. Admission authority still
requires an explicit authority decision. This scope changes none of the
repository's non-admitting role.

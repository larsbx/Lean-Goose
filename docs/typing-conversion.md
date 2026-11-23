# Typing and conversion: semantic scope

This fifth required scope connects successful execution of the Lean **model**
to independent typing and beta/zeta/delta reduction judgments. It compares both
actual models with complete compound-binding observations from the unchanged
Goose checker. A separate comparison uses the pinned native Lean and OCaml
engines. These are distinct forms of evidence: the model soundness theorems do
not establish arbitrary native implementation refinement.

The original increment built on `main` at
`632ab16805830aaf8ee94a4647dc948901e09423`, whose PR #5 source was
`de66c4198cdc01371d5593684bfdf07b7e1bef8c`. The owned checker, its derivation,
external pins, and four preceding model scopes retain their existing sources.
It was merged through [PR #6](https://github.com/larsbx/Lean-Goose/pull/6).
Execution results belong to the matching source-bound receipt, not to this scope
declaration. [Semantic environments](semantic-environment.md) now adds the
predecessor-certificate and record-preservation bridge as a sixth scope.

## Smallest useful fragment

The fragment uses the existing `GooseExpressionDag.Expr` without adding syntax.
Numeric sorts, variables, transparent constants, lambda, dependent Pi,
application, and typed let are all needed to expose the checker's compound
stored-field contract. Transparent delta reduction is necessary even when the
central target is beta/zeta: constant inference reads a stored declaration, and
conversion must unfold its original value.

The environment is an ordered list of bindings with `name`, `ty`, `value`, and
`inferred`. Contexts contain binder types, newest first. The semantic model does
not impose the native parser's numeral limits or model its caches and allocation.
The replay protocol and finite implementation profile have separate bounds.

| Syntax | Inference rule reflected in the model |
| --- | --- |
| `Sort u` | Infer `Sort (u+1)`. |
| Variable `i` | Look up its binder type and lift it by `i+1`, starting at cutoff zero. |
| Constant `c` | Infer the binding's original declared type, not its normalized stored `inferred` field. |
| Lambda `λ x:A. b` | Check that `A` has a sort, infer `b` under the extended context, and return a Pi. |
| Pi `Π x:A. B` | Check both sorts under their respective contexts; return sort zero if the codomain sort is zero, otherwise their maximum. |
| Application `f a` | Infer `f`, head-reduce its type to Pi, infer and convert the argument type to the domain, then substitute `a` into the codomain. |
| Typed let `let x:A := v; b` | Check the annotation's sort and the value's type, then infer the capture-avoiding substitution of `v` into `b`. |

Head reduction unfolds a constant's stored **original value**, removes a let by
substitution, or reduces a lambda application by substitution. Normalization
first head-reduces, then normalizes both children of applications, lambdas and
Pis. Conversion compares the resulting structures. Both models reuse their
existing capture-avoiding substitution infrastructure.

There is no eta rule, proof-irrelevance rule, general universe language,
inductive/recursor/quotient support, opaque or recursive declaration support,
or `.olean` ingestion in this fragment. The existing eta and proof-irrelevance
comparison specimens remain required and keep their registered differences.

## Successful checking and stored fields

The modeled definition pipeline follows `check_definition`:

1. Reject an existing name before semantic checking.
2. Require both original expressions to be closed.
3. Validate every constant in both original expressions.
4. Check that the declared type has a sort.
5. Infer the original value's type and normalize that inferred type.
6. Check conversion of the normalized inferred type to the original declared type.
7. Append the original name, declared type, original value and normalized inferred type.

Any refusal retains the entire previous binding list. Scope failure stops the
trace. The model's separate budget-exhaustion outcome also stops model replay;
it is never compared as a native semantic refusal.

For example, first define `U : Sort 2 := Sort 1`, then
`id : Π x:U. U := λ x:U. x`. The new binding must contain:

| Stored field | Required expression |
| --- | --- |
| `type` | The original Pi containing both occurrences of constant `U` |
| `value` | The original lambda whose domain is constant `U` |
| `inferred` | The normalized Pi with domain and codomain `Sort 1` |

The native comparison additionally requires `type` and `value` to retain their
original raw input IDs. A structurally identical replacement ID is refused by
the adapter. All earlier binding IDs and immutable node payloads must survive
both subsequent success and refusal.

Checking an expression and reducing it are different operations. An ordinary
lambda-application value can be typed by substituting its inferred codomain
without normalizing the value itself. The beta-chain fixtures therefore put
their redex chains in the **declared type**, where successful conversion forces
the native reduction path. Original value syntax remains observable.

### Rejection before erasure

An unused bad argument or let value is not licensed by its disappearance during
reduction. For example, `let x:Sort 1 := Sort 1; Sort 0` is refused because its
value has type `Sort 2`. Unknown constants in beta-erased arguments and
zeta-erased let values are rejected during validation of the original syntax.
A malformed declared type is checked before normalization could conceal it.

The common profile covers all five semantic refusal labels:
`Unknown_constant`, `Duplicate_definition`, `Expected_sort`,
`Expected_function`, and `Type_mismatch`. Native scope and competing-error
priority cases are separately identified, rather than assigning the pinned
Lean driver a stronger error-order contract than its existing interface.

## Lean proof increment

`formal/lean/TypingConversion.lean` defines independent, fuel-free relational
judgments `HeadReduces`, `Normalizes`, `Converts`, `Infers`, and `HasSort`.
`Converts E a b` means that both expressions have a common normalization result
under `E`. The judgments do not invoke the executable inference functions as
their defining premises.

The main result is successful-execution soundness:

```text
infer fuel E Γ e = ok A  ->  Infers E Γ e A
sortLevel fuel E Γ e = ok u  ->  HasSort E Γ e u
normal fuel E e = ok n  ->  Normalizes E e n
convertible fuel E a b = ok true  ->  Converts E a b
```

`inference_and_sort_sound` proves the mutually dependent inference/sort result.
Its application case uses the proven conversion bridge, and its let case uses
the existing capture-avoiding substitution operation. A successful
`checkValue` proves all three of the following:

- The original declared type has a sort in the empty context.
- There is an inferred type of the original value whose normalization is the stored inferred expression.
- The stored inferred expression converts to the original declared type.

`checked_success_has_semantics` extracts that semantic checker result from the
complete duplicate/scope/validation pipeline.
`stored_inferred_converts_to_declared` exposes its final conversion claim.
`success_stores_exact_fields` and `refusal_preserves_all_bindings` connect the
semantic result to the actual model environment transition.

The required inventory contains **32 new theorems**. It also includes context
lifting, the distinction between constant inference and delta unfolding,
beta/zeta substitution equations, beta-substitution scope preservation,
the codomain-zero Pi rule, unknown-constant non-erasure, duplicate priority,
explicit budget refusal, trace termination and absent admission authority.
The audit requires every named theorem's transitive axiom set to be empty and
checks the entire new namespace. Generated support may use only `propext`.

The inference soundness theorem quantifies over arbitrary finite model
environments and contexts. It is soundness for these operational judgments,
not a global well-formed-environment theorem for dependent type theory.
No claim of type preservation, normalization of every well-typed term,
conversion completeness or decidability follows from it alone.

## Quint and finite correspondence

The independent Quint model implements evaluation as a continuation machine.
Its syntax transformations use the previously required Quint DAG and
substitution definitions. The Python helper only validates input/output
framing and invokes actual Quint evaluation; it never computes a typing answer.
The model echoes the complete request identity, including raw node fields,
definition order, selectors and budget, before the helper projects its result.

The fifth gate requires **26 new deterministic tests**, a seeded run of
**1,000 samples with at most eight transitions**, and an exact two-state negative
witness. Exploration chooses two names and eight small expression/checking
forms, processes at most four snapshots, and stutters thereafter. It is not
exhaustive exploration of arbitrary DAGs or all terms within the replay limits.
The negative witness corrupts a successfully checked identity's stored inferred
Pi to `Sort 0` while retaining its original declared type and value. The
transition invariant must reject that precise corruption; an arbitrary process
failure does not satisfy the control.

| Required comparison | Inventory and observation |
| --- | --- |
| Actual Lean and actual Quint models | 48 authored JSONL requests, 67 input definitions, 66 processed snapshots; one later definition is suppressed by fatal scope failure. Complete fields must agree with each other and the authored examples. |
| Native Goose | The same 48 requests in both `--trace` and `--check`: 96 commands. Compare compound fields, original IDs, immutable prefixes, refusal state, and fatal process behavior. |
| Pinned native Lean and OCaml | 44 common-fragment fixtures, 59 ordered definition outcomes per engine, also compared with native Goose. No new registered semantic differences. External drivers do not expose the stored-field trace. |
| Strict replay refusals | 24 malformed requests through each actual helper, including malformed numerals, selectors, topology, duplicate/unknown keys and expansion bounds. |
| Model budget | Both helpers report dedicated code 9 on the zero-budget control; it cannot satisfy a native correspondence expectation. |

The four excluded external-reference cases are
`duplicate_precedes_scope`, `scope_halts_after_compound`,
`scope_precedes_unknown`, and `unknown_precedes_inference`. They are still
required native/model cases. The common profile tests dependent identity and
application, beta/zeta in declared types, compound alias chains, context reuse,
capture-sensitive substitution, impredicative Pi, refusal recovery and all
designated semantic refusal categories.

## Budgets, provenance, and reproduction

The Lean executable model decreases a recursion-depth budget. The Quint
machine reproduces this budget and has an additional 2,048-transition execution
cap per evaluator call. Model recursion exhaustion is code 9. Internal machine
cap exhaustion is code 10 and makes the helper fail without a semantic result.
Neither is the native checker's work counter, height/index/node cap, or code-7
resource result. The 48 native cases use model recursion budget 128 and must
complete within both evaluators' envelopes.

The [replay contract](../schemas/typing-conversion-replay-v1.md) declares
node/definition/budget bounds and the 65,536 aggregate expanded input-token
limit. Native diagnostic decoding separately enforces the existing 4 MiB trace
limit and rejects structural expansion beyond one million tokens for any
expression or two million across a decoded table. Exceeding any observation
envelope fails the gate; it does not omit a case or invent a checking result.

Use the existing pinned setup from [validation.md](validation.md), then run:

```sh
make acceptance
```

`tools/check_formal.py` executes all six scopes and writes formal evidence v6.
`tools/run.py check` retains the existing **964 ordered outcomes per engine**,
16 fixtures and six parser/resource controls, and records the new 44-fixture
comparison separately as `typing_conversion`. Benchmark smoke retains its
existing seven families and makes no new speed claim.

The formal receipt records the new axiom audit, deterministic tests, bounded
run, negative witness, replay contracts, inputs, native commands and full output
streams. Complete replay and native-comparison logs are compressed under
`conformance/evidence/formal/typing-*`. The conformance receipt retains actual
reference-engine stdout, stderr and commands for the new cases. The enclosing
gates verify source, dependency and executable identities and require sources
to remain unchanged during execution. Hosted CI remains separate evidence.

## Remaining semantic obligations

1. The [semantic-environment scope](semantic-environment.md) now proves
   predecessor certification, its preservation across traces, environment
   weakening of the judgments and the complete-record bridge. Next prove
   inferred-field closedness/availability and valid binder-context invariants.
2. Prove suitable completeness with sufficient model budget, deterministic
   normal forms, typed beta/zeta preservation, and normalization/termination for
   a precisely stated admissible fragment. Successful-execution soundness is
   already a narrower theorem and does not discharge these obligations.
3. Refine actual Goose inference, head/normal reduction, conversion, binding
   lookup and validation to the model for arbitrary admissible inputs. Relate
   concrete DAG allocation, context restoration and cached results to the
   structural judgments, including refusal behavior.
4. Model native work, height, index, allocation and parser bounds, and prove
   failure priority around duplicate lookup and later semantic checks. Current
   budget exhaustion is deliberately a distinct model observation.
5. Establish the diagnostic serializer/compiler/parser trust boundary and the
   connection to Lean's kernel semantics beyond finite external observations.
   Unsupported Lean features retain their existing boundaries.

The repository remains a research candidate with
`acceptance_authority = false`.

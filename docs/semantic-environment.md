# Semantic environment preservation

This sixth formal scope builds on the typing soundness established in
[PR #6](https://github.com/larsbx/Lean-Goose/pull/6). It proves that the existing
typing model builds environments whose stored bindings have independent
semantic derivations, and that later successful or refused checks preserve
those derivations and the scope of all three stored fields. It connects the
resulting records to the earlier full-record preservation model.

[PR #7](https://github.com/larsbx/Lean-Goose/pull/7) introduced predecessor
certification at merge revision `8ded5c39faa52ad58743d7c5fdfe09049398ed62`.
The current gate extends that proof with inferred-field and local context
scope. Its source-bound acceptance receipt records execution on the extended
source.

## Independent semantic predicate

`BindingValidIn environment binding` requires all of the following:

1. The **original declared type and value** are closed expressions.
2. Every constant occurring in either original expression resolves in the
   specified environment. This includes branches that beta or zeta would erase.
3. The declared type has a sort, witnessed by the independent `HasSort` judgment.
4. Some actual type is derived for the original value by `Infers`, and that
   actual type `Normalizes` to the stored inferred field.
5. The stored inferred field `Converts` to the original declared type.

These are the existing relational judgments from `TypingConversion.lean`.
The predicate is not defined as successful executable checking. The theorem
`checked_success_certifies_binding` connects actual successful model checking
to this independent predicate.

`Certified` is an inductive ordered-environment predicate. Its empty case is
the empty environment. Its append case requires a certified predecessor, a
fresh name, and `BindingValidIn` **in that exact predecessor**. A binding cannot
justify itself or rely on a later declaration.

## Preservation beyond historical certificates

`LookupExtends before after` preserves the complete binding selected by every
previously successful lookup. Fresh append satisfies this relation; refusals
retain the same environment. The Lean development proves weakening along it
for `HeadReduces`, `Normalizes`, `Converts`, `Infers`, and `HasSort`. It transports
derivations without assuming an executable checker equation or enumerating
expressions.

| Required theorem | Claim |
| --- | --- |
| `checked_success_certifies_binding` | Successful checking establishes the independent certificate in the predecessor environment |
| `step_preserves_certification` | Success appends a certified binding; refusal preserves the old certification |
| `certified_lookup_valid` | A selected binding has the required derivations in the **current** certified environment |
| `run_snapshots_certified` | Every processed snapshot of an arbitrary finite definition trace is certified |
| `run_final_environment_certified` | A trace from a certified start ends in a certified environment |
| `run_preserves_lookup` | Every earlier successful full-record lookup survives the trace |
| `run_preserves_semantic_judgments` | Earlier binding certificates remain valid in the final environment |
| `empty_run_has_semantic_environment` | Empty-start endpoint, including refusal and fatal-prefix behavior |

These statements quantify over arbitrary finite expressions, definition lists,
and model budgets. An arbitrary initial environment must satisfy `Certified`
where that premise is stated. Lookup and record-preservation lemmas that do not
need this premise are formulated without it. Fatal scope or model budget
exhaustion stops the suffix according to the unchanged typing model. No native
resource accounting is inferred from the model budget.

The required inventory is **64 named Lean theorems**, including 27 about
inferred-field scope and its prerequisites and controls. Required theorem
closures are empty. The gate also audits supporting declarations in both
namespaces, including private lemmas. See
[`SemanticEnvironmentAudit.lean`](../formal/lean/SemanticEnvironmentAudit.lean).

## Inferred fields and local contexts

[`EnvironmentScope.lean`](../formal/lean/EnvironmentScope.lean) proves the
following statement for any model fuel and successful check.

```lean
theorem checked_success_inferred_scope_of_closed_values
    (fuel : Nat) (environment : Environment) (definition : Definition)
    (stored : Expr) (values : LookupValuesClosed environment)
    (success : checked fuel environment definition = .ok stored) :
    Closed stored ∧ Available environment stored
```

`LookupValuesClosed` asks only that every binding selected by `find` have a
closed **original value**. Delta reduction reads that field. Closedness of the
new original declaration comes directly from `checked`. The existing
certificate gives a normalization of the actual inferred type to the stored
field and conversion of that field to the original declaration.
`normalization_yields_normal_form` proves that the stored field has no
constants, typed lets, or beta redexes. Every normalization of such a form
returns it unchanged. The common conversion result is therefore the stored
field and inherits scope from normalization of the closed declared type.
Availability follows from the shape of full normal forms in this fragment.
The proof uses neither a sort witness for every old binding nor any invariant
on old cached inferred fields.

Dropping the lookup-value premise fails to give a uniform guarantee over
arbitrary supplied environments. In the Lean and Quint controls, a forged
environment contains a single `A` with declared type `Sort 1`, original value
`#0`, and inferred field `Sort 1`. Checking the closed declaration
`id : (Π (_ : A), A) := fun x : A => x` succeeds with
`Π (_ : #0), #0` stored. The domain's `#0` is loose. A second control uses a
forged original type with a loose index in an erased zeta argument. Its raw
inferred type is open, while the normalized stored field is closed. These
environments are supplied directly to the models.

`checked_success_inferred_closed_available` specializes the theorem to
`Certified`. Certification and existing prefix preservation then give all
three field properties for every record in every processed snapshot and the
final environment, including refusal and fatal stopping. The original
type and value still require constant availability in the exact predecessor.

`ContextValid` stores innermost binders first and requires each entry to be
scoped, available, and assigned a sort in its preceding outer tail.
`inference_preserves_scope_available` only needs `ContextScoped`, the
structural part of that invariant, along with a scoped and available input.
Old selected declared types and old delta values must be closed and
available. Variable lookup lifts an entry by its index plus one, including its
own binder. The dependent context `[#0, Sort 1]` admits that lift.
`[#0]` is structurally invalid and raw inference in it returns an out-of-scope
`#1`. A closed lambda serves as a separate control for an in-scope entry that
lacks a sort. `valid_context_inference_scope` is the certified, sorted-context
specialization.

## Bridge to complete stored records

`projectBinding` constructs a `GooseStoredBindings.Binding`. It applies the
existing structural expression encoder independently to the declared type,
original value, and stored inferred type. Payload and append preservation are
exact equalities.

The old model names bindings by natural numbers; the typing model uses lists
of name bytes. The bridge takes `nameCode : List Nat → Nat`. Lookup correspondence
explicitly requires this function to be injective. Payload and indexed-prefix
preservation do not need that assumption. This increment does not prove a
particular wire name encoder injective for every input.

`projected_trace_preserves_old_record` directly applies the earlier
`GooseStoredBindings.bindingAt_append_preserves` theorem to the exact projected
suffix. `projected_lookup_corresponds` and `projected_trace_preserves_lookup`
connect both lookup interfaces under the stated name-coding premise.

The target model permits arbitrary payload vectors. This bridge uses the full
expression encoder, including length-framed constant names. It does not identify
that wire with the older small Sort/Const fixture convention, and does not
simulate the older model's four abstract checking actions.

## Quint checks and exact negative control

[`SemanticEnvironment.qnt`](../formal/quint/SemanticEnvironment.qnt) imports the
unchanged typing and stored-binding models. Each insertion freezes its complete
predecessor, stored binding, and separate observations of declared-sort checking,
value inference, normalization into the inferred field, and the two normal
forms witnessing conversion. Certificate validity checks these component
equations, closedness and constant availability of all three fields, and that
re-normalizing the stored inferred field returns that field.

The state invariant checks ordered certificate/record correspondence, exact
predecessor prefixes, distinct names, old records and lookups, refusal atomicity,
fatal stopping, and the same semantic observations in the final environment.
It also checks payload and lookup projection into `StoredBindings`. Sampled
name coding uses radix 257 with a nonzero leading sentinel; finite checks do
not discharge the generic Lean injectivity premise.

The gate requires **31 deterministic tests** and **1,000 sampled traces of at
most eight transitions**, seed `20261123`, on the TypeScript backend. Simulation
uses three destination names and nine input forms, processes at most four
snapshots, and stutters thereafter. These finite checks are not an unbounded
Quint theorem or an independent proof of the imported semantic evaluator.

The negative control starts with valid `U : Sort 2 := Sort 1` and an identity
over `U`. It successfully adds `V : Sort 2 := U`, then corrupts the **old**
`U.value` to `Sort 0`. Frozen certificates and earlier snapshots stay intact.
The gate requires the exact two-state ITF witness, complete predecessor and
certificate fields, the expected violation diagnostic, and exit code 1.
An unrelated failure or different mutation cannot satisfy the control.

## Finite implementation observations

The authored profile covers **15 histories, 75 input definitions, and 73 processed
snapshots**. It includes compound aliases, aliases in declared types, dependent
applications, beta/zeta declarations, forward and self references, refusal/retry
sequences, duplicate replacement attempts, and fatal stopping. Three histories
exercise specialization under three binders, conversion refusal followed by retry,
and a dependent binder annotation outside its outer context.

The unchanged actual Lean and Quint typing replay helpers evaluate these
histories through the existing
[typing replay contract](../schemas/typing-conversion-replay-v1.md). Native Goose
executes `--trace` and `--check` for each, for **30 native commands**. Comparison
requires all stored fields, original type/value IDs, immutable binding and
raw-node prefixes, ordered outcomes, and exact fatal process status. The native
interface exposes stored records, not semantic proof certificates.

Twelve common-reference histories additionally produce **62 ordered outcomes per
engine** for actual Goose, pinned Lean, and pinned OCaml. Fatal scope and
duplicate-before-invalid-scope histories remain native/model-only controls.
No new semantic disagreement is allowed. This profile is recorded separately
from the prior 964 outcomes and the fifth scope's 59 outcomes per engine.

## Remaining obligations

Typed context weakening and substitution, subject reduction, arbitrary
reduction determinacy, conversion laws, sufficient-budget completeness, and
normalization of every well-typed term remain open. Context validity currently
supplies structural preservation of inferred types. A sort witness for each
inferred type and preservation of typing across substitutions require further
metatheory.

General native inference/reduction/lookup refinement, serializer correctness,
cache/resource semantics, parser/compiler trust, and full Lean kernel
compatibility remain separate obligations. Eta, proof irrelevance, general
universes, inductives, recursors, quotients, and other unsupported features keep
their boundaries. `acceptance_authority` remains `false`.

# Typed binder-context weakening

`ContextInsertion E k Γ Γ′` inserts at cutoff `k` in a context written
innermost first. At cutoff zero, the annotation must be scoped and have
available constants in its outer tail, and it must have a `HasSort` derivation
there. Crossing a newer entry increments the cutoff and lifts that entry's
annotation at the previous cutoff. Older entries keep their raw annotations.

For a certified environment, [the Lean proof](../formal/lean/ContextWeakening.lean)
establishes the following endpoints.

| Endpoint | Conclusion under `ContextInsertion E k Γ Γ′` |
| --- | --- |
| `inference_lift` | `Infers E Γ t T` gives `Infers E Γ′ (lift 1 k t) (lift 1 k T)`. |
| `sort_lift` | `HasSort E Γ t u` gives `HasSort E Γ′ (lift 1 k t) u`. |
| `ContextInsertion.preserves_valid` | `ContextValid E Γ` gives `ContextValid E Γ′`. |

The variable proof relates the annotation fetched at the new index to the
original annotation after both lookup's lift and the insertion lift. It
commutes those lifts to establish equality of the inferred types. Applications and
lets use a second commutation law. Lifting a substituted expression lifts the
replacement at the outer cutoff and lifts the original body one slot deeper.
Weak-head reductions and common normal forms lift under closed original delta
values. The constant inference case also uses closed declared types. The
certified environment supplies both premises.

The result preserves the literal lifted type. The conversion required by an
application or let is its original comparison, transported by lifting both
normalization derivations to the same lifted result. Context validity uses the
existing `lift_scope` and `lift_preserves_available` lemmas alongside
`sort_lift` for every retained annotation.

## Controls

[The Lean controls](../formal/lean/ContextWeakeningControls.lean) include
insertion of `y : A` between `x : A` and `A : Sort 1`. The raw context changes
from `[var 0, sort 1]` to `[var 1, var 0, sort 1]`. The index of `x` stays at
zero and its inferred type becomes `var 2`. A polymorphic application and a
separate let containing a Pi exercise lifting under binders and through
dependent result types. The stale context `[var 0, var 0, sort 1]` has structural
scope and fails `ContextValid`. Further controls reject a self-reference and a
closed lambda used as a binder annotation. Forged environments supply separate
failures for open declared types and open delta values.

The semantic-environment replay includes closed definitions expressing the
before and after dependent applications, a stale-annotation refusal with
successful retry, and beta and zeta cases with reducible annotations.
These are finite evaluator and native observations of the same examples.

## Typed substitution and subject reduction

Write the source context as `newer ++ (A :: outer)`, with
`k = newer.length`. Substitution removes the selected slot. It substitutes
through each newer annotation at the number of intervening entries, leaving
the older tail as stored. The proof should start with a valid source context
and a replacement in `outer` that infers `R` with `Converts E R A`. Deriving
validity of the transported context requires a sort for each transported newer
annotation in its new tail. Carry scope and availability for the replacement
and the terms whose structural scope is used when extending a context.

- **Selected variable.** `substitution_hit` already handles this case assuming
  a valid target prefix. Repeated weakening transports the replacement and
  its conversion through the newer entries. The inferred replacement type is
  `lift k 0 R` and it converts to `lift k 0 A`, the substitution of the original
  lookup type `lift (k + 1) 0 A`.
- **General derivations.** The intended inference conclusion supplies an
  actual inferred type convertible to `substitute replacement k T`.
  The paired sort conclusion retains the level. Binder cases need sort
  transport in their new tails, and dependent bodies may need context
  conversion when their annotations are compared through conversion.
  Application needs to recover a Pi head from the new function type, compare
  its domain to the argument's inferred type, and relate the corresponding
  codomains after instantiation. Sort transport similarly needs the sort head
  at the original numeric level. These steps require compatibility of
  head reduction and conversion with admissible substitution and the Pi and
  sort inversion laws on the normal forms used by the derivations. The
  neutral-head control shows why a blanket equality of substituted head
  results fails. A typed replacement can expose a redex, so the substituted
  result may need further reduction.
- **Literal beta.** `literal_beta_premises` extracts the annotation's sort,
  the body derivation, the argument inference and its conversion to the
  domain, and the exact expected codomain `substitute arg 0 bodyType`.
  The missing proof is typed substitution at these premises. The certified
  empty-environment control `literal_beta_requires_conversion` checks that
  the reduct can infer `Sort 1` while the redex infers a let annotation that
  normalizes to `Sort 1`. Subject reduction therefore needs a typing
  conclusion up to conversion. A function that first reduces to a lambda
  additionally needs typed preservation for those function steps and the
  comparison of the resulting Pi with the original application type.
- **Immediate zeta.** `zeta_inference` and `zeta_sort` already preserve the
  exact inferred type and level. The existing let typing rule contains the
  derivation of the substituted body. Deriving the same property for further
  weak-head steps needs preservation for those steps. A let formulation that
  types its body under the annotation would instead use the general
  substitution theorem to establish the contraction.

An inferred-type sort witness remains open for general relational inference.
Full head or normalization preservation also needs delta, using the certified
original value derivation and its conversion to the declared type, and the
dependent congruence cases. The shared-normal-form definition of
`Converts` makes the necessary normalization witnesses explicit.

# Transition of the all-length non-commutation route (2026-08-27)

This note records the simplification of the active periodic-sector proof route
in `TNLean/MPS/MPDO/CyclicProjector.lean`. The old all-length interface has no
non-`Archive` Lean consumers, but it is public and incomparable with the new
existential-length interface. Its three declarations therefore remain as
deprecated compatibility API rather than being deleted. The two obsolete
blueprint leaf entries are removed because production exposition uses the
newer route.

## Transitioned declarations

| Deprecated declaration | Preferred route |
|---|---|
| `MPOTensor.NoninvariantProjectorNoncommuting` | supply the single-length existential hypothesis of `MPOTensor.hasNoPeriodicVectors_verticalTensor_of_exists_not_commute_of_displaced` when it is available |
| `MPOTensor.periodicVectorYieldsCyclicProjector_of_noncommutation` | use `MPOTensor.exists_displaced_invariant_projector_of_periodic_vector` and a problem-specific noncommutation theorem |
| `MPOTensor.hasNoPeriodicVectors_verticalTensor_of_noncommutation` | `MPOTensor.hasNoPeriodicVectors_verticalTensor_of_exists_not_commute_of_displaced`, or `MPOTensor.hasNoPeriodicVectors_verticalTensor_of_horizontalCF` under normalized BNT-refined horizontal form |

## Compatibility retention is required despite absent consumers

Neither the deprecated nor the preferred hypothesis implies the other.
`NoninvariantProjectorNoncommuting` quantified over Hermitian idempotents `Q`
only, and demanded non-commutation with the density operator at *every* chain
length. The surviving
`hasNoPeriodicVectors_verticalTensor_of_exists_not_commute_of_displaced`
quantifies over *every* idempotent `Q` and demands only that *some* chain
length be noncommuting. Weakening the length quantifier and strengthening the
projector quantifier move in opposite directions, so the two hypotheses are
incomparable. Nothing in the production corpus cites the deprecated
statements, but external clients may satisfy only the Hermitian all-length
hypothesis. Keeping
the exact declarations preserves that API during the transition window.

## Blueprint

Two obsolete entries in
`blueprint/src/chapter/ch20_mpdo_canonical_forms_periodic_sectors.tex` were
deleted with their proofs, both leaves in the dependency graph:

* `def:mpdo_noninvariant_projector_noncommuting` — referenced only by the
  `\uses` list of the entry below;
* `thm:mpdo_cyclic_projector_of_noncommutation` — referenced by nothing.

`thm:mpdo_vertical_no_periodic_vectors_injective` and
`thm:mpdo_cyclic_projector_reduction` are unaffected and keep their tags. The
all-length condition remains stated in blueprint prose inside
`def:mpdo_periodic_vector_yields_cyclic_projector`, so no mathematical content
leaves the exposition.

## Paper-gap note

`docs/paper-gaps/cpgsv17_periodic_sector_projector.tex` now distinguishes the
source projector's surviving all-length field
`MPOTensor.PeriodicSectorProjector.not_commute` from the stronger uniform
predicate retained here for compatibility. The active proofs use neither the
uniform predicate nor an all-length hypothesis.

## Deferred follow-on

The `StackedLayers` closure is left for a separate change. After this
retirement the only Lean call site of
`MPOTensor.hasNoPeriodicVectors_verticalTensor_of_cyclicProjector` is gone, but
that theorem is still tagged inside `thm:mpdo_cyclic_projector_reduction`,
which also tags the live `MPOTensor.periodicVectorYieldsProjector_of_cyclic`;
and `MPOTensor.PeriodicVectorYieldsCyclicProjector` is tagged by its own
blueprint definition and is referenced from `PeriodicExclusion.lean`. Unwinding
those requires redirecting or deleting two further blueprint entries.

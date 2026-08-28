# Deletion of the all-length non-commutation route (2026-08-27)

This note records the simplification of the active periodic-sector proof route
in `TNLean/MPS/MPDO/CyclicProjector.lean`. The old all-length interface has no
non-`Archive` Lean consumers. Under TNLean's explicit no-public-API-
compatibility policy, its predicate and two wrapper theorems are deleted
directly rather than retained as deprecated declarations. The two obsolete
blueprint leaf entries remain removed because production exposition uses the
newer route.

## Deleted declarations

| Deleted declaration | Surviving route |
|---|---|
| `MPOTensor.NoninvariantProjectorNoncommuting` | supply the single-length existential hypothesis of `MPOTensor.hasNoPeriodicVectors_verticalTensor_of_exists_not_commute_of_displaced` when available |
| `MPOTensor.periodicVectorYieldsCyclicProjector_of_noncommutation` | use `MPOTensor.exists_displaced_invariant_projector_of_periodic_vector` and a problem-specific noncommutation theorem |
| `MPOTensor.hasNoPeriodicVectors_verticalTensor_of_noncommutation` | `MPOTensor.hasNoPeriodicVectors_verticalTensor_of_exists_not_commute_of_displaced`, or `MPOTensor.hasNoPeriodicVectors_verticalTensor_of_horizontalCF` under normalized BNT-refined horizontal form |

The former and surviving hypotheses are incomparable: the deleted predicate
quantified only over Hermitian idempotents but required non-commutation at every
chain length, whereas the surviving existential-length theorem quantifies over
every idempotent and requires one noncommuting length. That distinction remains
part of the audit record, but it does not justify restoring a compatibility
surface in a project that promises none.

## Blueprint

Two obsolete leaf entries in
`blueprint/src/chapter/ch20_mpdo_canonical_forms_periodic_sectors.tex` were
already deleted with their proofs:

* `def:mpdo_noninvariant_projector_noncommuting`;
* `thm:mpdo_cyclic_projector_of_noncommutation`.

`thm:mpdo_vertical_no_periodic_vectors_injective` and
`thm:mpdo_cyclic_projector_reduction` are unaffected and keep their tags. The
all-length condition remains stated in blueprint prose inside
`def:mpdo_periodic_vector_yields_cyclic_projector`, so no mathematical content
leaves the exposition.

## Paper-gap note

`docs/paper-gaps/cpgsv17_periodic_sector_projector.tex` distinguishes the
source projector's surviving all-length field
`MPOTensor.PeriodicSectorProjector.not_commute` from the deleted stronger
uniform predicate. The active proofs use neither a uniform predicate nor an
all-length hypothesis.

## Completed follow-on

The zero-call-site `StackedLayers` closure
`MPOTensor.hasNoPeriodicVectors_verticalTensor_of_cyclicProjector` is deleted
directly under the no-public-API-compatibility policy. Its tag is removed from
`thm:mpdo_cyclic_projector_reduction`, which continues to tag the live
`MPOTensor.periodicVectorYieldsProjector_of_cyclic`; the live predicate
`MPOTensor.PeriodicVectorYieldsCyclicProjector` keeps its own blueprint
definition and remains the interface referenced from `PeriodicExclusion.lean`.
No private dependency became dead: the surviving reduction theorem uses the
predicate and `periodicSectorProjectorOfCyclicData` directly.

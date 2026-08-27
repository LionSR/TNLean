# Retirement of the all-length non-commutation route (2026-08-27)

This note records three deletions in `TNLean/MPS/MPDO/CyclicProjector.lean`,
taken under the pass-through exception of `docs/project_conventions.md` §Style.
Each removal has zero non-`Archive` Lean consumers, and both blueprint entries
whose `\lean{...}` tags named a removed declaration were deleted in the same
change.

## Removed declarations

| Removed declaration | Replacement |
|---|---|
| `MPOTensor.NoninvariantProjectorNoncommuting` | none needed; the surviving route states its single-length condition inline, as the existential hypothesis of `MPOTensor.hasNoPeriodicVectors_verticalTensor_of_exists_not_commute_of_displaced` |
| `MPOTensor.periodicVectorYieldsCyclicProjector_of_noncommutation` | none needed; `MPOTensor.exists_displaced_invariant_projector_of_periodic_vector` supplies the projector, its word invariance, and its displacement unconditionally |
| `MPOTensor.hasNoPeriodicVectors_verticalTensor_of_noncommutation` | `MPOTensor.hasNoPeriodicVectors_verticalTensor_of_exists_not_commute_of_displaced`, and for a tensor in normalized BNT-refined horizontal form `MPOTensor.hasNoPeriodicVectors_verticalTensor_of_horizontalCF` |

## The removal is justified by absent consumers, not by subsumption

Neither the removed nor the surviving statement implies the other.
`NoninvariantProjectorNoncommuting` quantified over Hermitian idempotents `Q`
only, and demanded non-commutation with the density operator at *every* chain
length. The surviving
`hasNoPeriodicVectors_verticalTensor_of_exists_not_commute_of_displaced`
quantifies over *every* idempotent `Q` and demands only that *some* chain
length be noncommuting. Weakening the length quantifier and strengthening the
projector quantifier move in opposite directions, so the two hypotheses are
incomparable. Nothing in the production corpus cited the removed statements, so
no downstream result loses a proved fact.

## Blueprint

Two entries in
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

`docs/paper-gaps/cpgsv17_periodic_sector_projector.tex` described the removed
predicate in its Status section. That sentence now names the all-length
condition mathematically — a displaced orthogonal projector failing to commute
with the density operator at every chain length, printed at source line 1889 —
and records that neither proof uses it and that it is not formalized.

## Deferred follow-on

The `StackedLayers` closure is left for a separate change. After this
retirement the only Lean call site of
`MPOTensor.hasNoPeriodicVectors_verticalTensor_of_cyclicProjector` is gone, but
that theorem is still tagged inside `thm:mpdo_cyclic_projector_reduction`,
which also tags the live `MPOTensor.periodicVectorYieldsProjector_of_cyclic`;
and `MPOTensor.PeriodicVectorYieldsCyclicProjector` is tagged by its own
blueprint definition and is referenced from `PeriodicExclusion.lean`. Unwinding
those requires redirecting or deleting two further blueprint entries.

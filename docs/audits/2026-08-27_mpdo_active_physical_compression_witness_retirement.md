# Active physical-compression witness deletion

This audit records the direct deletion of
`MPOTensor.PhysicalSectorFactorization.ActivePhysicalCompressionWitness` and
its entire namespace API. TNLean does not promise public API compatibility, so
none of the former structure, constructors, projections, or theorem wrappers is
retained as a deprecated declaration.

The surviving implementation uses the underlying declarations directly:

| Deleted compatibility API | Surviving API |
|---|---|
| `MPOTensor.PhysicalSectorFactorization.ActivePhysicalCompressionWitness` | `MPOTensor.PhysicalSectorFactorization.ActiveFactorSupportData` |
| `…ActivePhysicalCompressionWitness.canonical` | `MPOTensor.PhysicalSectorFactorization.activeFactorSupportData` |
| `…ActivePhysicalCompressionWitness.restrictionData` | `MPOTensor.PhysicalSectorFactorization.activePhysicalSupportRestrictionData` |
| `…ActivePhysicalCompressionWitness.factorization` | `MPOTensor.PhysicalSectorFactorization.activeRestrictedPhysicalSectorFactorization` |
| `…ActivePhysicalCompressionWitness.factorizationForRestrictionData` | the same, with the restricted-tensor type written as an ascription when needed |
| `…ActivePhysicalCompressionWitness.sectorCorrespondence` | `MPOTensor.PhysicalSectorFactorization.activeSectorFinEquiv` |
| `…ActivePhysicalCompressionWitness.neighboringOperator_eq_congruence` | `…activeRestrictedPhysicalSectorFactorization_neighboringOperator_eq_congruence` |
| `…ActivePhysicalCompressionWitness.neighboringOperator_posSemidef` | `…activeRestrictedPhysicalSectorFactorization_neighboringOperator_posSemidef` |
| `…ActivePhysicalCompressionWitness.neighboringOperator_trace` | `…activeRestrictedPhysicalSectorFactorization_neighboringOperator_trace` |
| `…ActivePhysicalCompressionWitness.neighboringTraceFactorization` | `…activeRestrictedPhysicalSectorFactorization_neighboringTraceFactorization` |

The two relocated declarations carrying mathematical content keep their
`**Scope restriction (active physical support compression):**` markers and
citations of
`docs/paper-gaps/cpsv16_active_physical_support_compression.tex` verbatim.

## What was checked

The in-tree call site,
`exists_etaLocalStructureData_supported_of_twoSidedPhysicalSlice` in
`TNLean/MPS/MPDO/PhysicalSectorActiveBond.lean`, already uses the surviving
declarations directly. Its restricted factorization keeps an explicit type
ascription, which supplies the type-level behavior formerly exposed by
`factorizationForRestrictionData`.

The relocated trace factorization applies `sum_mul_activeSectorFinEquiv`
directly. Neither relocated name collides in the enclosing namespace, checked
against `compressedNeighboringOperator_trace` and the other
`*_neighboringTraceFactorization` declarations of the MPDO modules.

## Blueprint

`thm:mpdo_active_physical_sector_neighboring_positivity` in
`blueprint/src/chapter/ch21_mpdo_rfp_simple_local_structure_capstone.tex` uses
the surviving declarations. No blueprint tag requires the deleted structure
surface, so the `\leanok` status and mathematical prose are unchanged.

`docs/paper-gaps/cpsv16_active_physical_support_compression.tex` cites the
surviving relocated trace-factorization name by `\leanid`.

# Active physical-compression witness retirement

This audit records the repository-local pass-through exception of
`docs/project_conventions.md` §Style. `ActivePhysicalCompressionWitness` was a
structure with a single field — a choice of factor-support coordinates —
wrapped in a namespace of eight members, seven of which forwarded to an
existing declaration of the enclosing namespace. It had one call site.

| Removed | Replacement |
|---|---|
| `MPOTensor.PhysicalSectorFactorization.ActivePhysicalCompressionWitness` | `MPOTensor.PhysicalSectorFactorization.ActiveFactorSupportData`, its only field |
| `…ActivePhysicalCompressionWitness.canonical` | `MPOTensor.PhysicalSectorFactorization.activeFactorSupportData` |
| `…ActivePhysicalCompressionWitness.restrictionData` | `MPOTensor.PhysicalSectorFactorization.activePhysicalSupportRestrictionData` |
| `…ActivePhysicalCompressionWitness.factorization` | `MPOTensor.PhysicalSectorFactorization.activeRestrictedPhysicalSectorFactorization` |
| `…ActivePhysicalCompressionWitness.factorizationForRestrictionData` | the same, with the restricted-tensor type written as an ascription at the one call site |
| `…ActivePhysicalCompressionWitness.sectorCorrespondence` | `MPOTensor.PhysicalSectorFactorization.activeSectorFinEquiv` |
| `…ActivePhysicalCompressionWitness.neighboringOperator_eq_congruence` | `…activeRestrictedPhysicalSectorFactorization_neighboringOperator_eq_congruence` |
| `…ActivePhysicalCompressionWitness.neighboringOperator_posSemidef` | `…activeRestrictedPhysicalSectorFactorization_neighboringOperator_posSemidef` |
| `…ActivePhysicalCompressionWitness.neighboringOperator_trace` | `…activeRestrictedPhysicalSectorFactorization_neighboringOperator_trace`, the same statement relocated to the enclosing namespace |
| `…ActivePhysicalCompressionWitness.neighboringTraceFactorization` | `…activeRestrictedPhysicalSectorFactorization_neighboringTraceFactorization`, the same construction relocated to the enclosing namespace |

The last two carried real mathematical content and were relocated rather than
deleted, keeping both `**Scope restriction (active physical support
compression):**` markers and their citations of
`docs/paper-gaps/cpsv16_active_physical_support_compression.tex` verbatim.

## What was checked

The single call site,
`exists_etaLocalStructureData_supported_of_twoSidedPhysicalSlice` in
`TNLean/MPS/MPDO/PhysicalSectorActiveBond.lean`, now names the underlying
declarations directly. Its restricted factorization keeps an explicit type
ascription: that ascription was the entire content of the removed
`factorizationForRestrictionData`, and without it the argument check of
`exists_etaLocalStructureData_lifted_supported_of_physicalSectorFactorization`
would rest on unification unfolding the restriction rather than on a checked
type.

The `sum_mul` field of the relocated trace factorization now applies
`sum_mul_activeSectorFinEquiv` directly; its former `simp` step existed only to
unfold the removed sector-correspondence alias.

Neither relocated name collides in the enclosing namespace, which was checked
against `compressedNeighboringOperator_trace` and the other
`*_neighboringTraceFactorization` declarations of the MPDO modules.

## Blueprint

`thm:mpdo_active_physical_sector_neighboring_positivity` in
`blueprint/src/chapter/ch21_mpdo_rfp_simple_local_structure_capstone.tex`
tagged four of the removed names. The structure itself and
`factorizationForRestrictionData` are subsumed by
`activeRestrictedPhysicalSectorFactorization`, which the same tag already
carries, so those two entries were dropped; the trace identity and the trace
factorization were redirected to their relocated names. The `\leanok` and the
prose are untouched — the prose never mentioned a witness.

`docs/paper-gaps/cpsv16_active_physical_support_compression.tex` cited the
removed trace factorization by `\leanid`; that citation was repointed to the
relocated name.

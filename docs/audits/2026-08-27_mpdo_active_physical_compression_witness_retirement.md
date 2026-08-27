# Active physical-compression witness deprecation

This audit records the migration away from
`MPOTensor.PhysicalSectorFactorization.ActivePhysicalCompressionWitness`.
The structure and all of its namespace members remain available under their
original qualified names as deprecated compatibility declarations. They are
retained because this was a public, blueprint-tagged API whose structure
surface is not reproduced by `ActiveFactorSupportData`.

New code should use the underlying declarations directly:

| Deprecated compatibility API | Preferred API |
|---|---|
| `MPOTensor.PhysicalSectorFactorization.ActivePhysicalCompressionWitness` | `MPOTensor.PhysicalSectorFactorization.ActiveFactorSupportData`, stored in its `factorSupport` field |
| `…ActivePhysicalCompressionWitness.canonical` | `MPOTensor.PhysicalSectorFactorization.activeFactorSupportData` |
| `…ActivePhysicalCompressionWitness.restrictionData` | `MPOTensor.PhysicalSectorFactorization.activePhysicalSupportRestrictionData` |
| `…ActivePhysicalCompressionWitness.factorization` | `MPOTensor.PhysicalSectorFactorization.activeRestrictedPhysicalSectorFactorization` |
| `…ActivePhysicalCompressionWitness.factorizationForRestrictionData` | the same, with the restricted-tensor type written as an ascription when needed |
| `…ActivePhysicalCompressionWitness.sectorCorrespondence` | `MPOTensor.PhysicalSectorFactorization.activeSectorFinEquiv` |
| `…ActivePhysicalCompressionWitness.neighboringOperator_eq_congruence` | `…activeRestrictedPhysicalSectorFactorization_neighboringOperator_eq_congruence` |
| `…ActivePhysicalCompressionWitness.neighboringOperator_posSemidef` | `…activeRestrictedPhysicalSectorFactorization_neighboringOperator_posSemidef` |
| `…ActivePhysicalCompressionWitness.neighboringOperator_trace` | `…activeRestrictedPhysicalSectorFactorization_neighboringOperator_trace` |
| `…ActivePhysicalCompressionWitness.neighboringTraceFactorization` | `…activeRestrictedPhysicalSectorFactorization_neighboringTraceFactorization` |

The compatibility wrappers preserve the former signatures and behavior while
delegating to `ActiveFactorSupportData` and the relocated declarations. The two
relocated declarations carrying mathematical content keep their
`**Scope restriction (active physical support compression):**` markers and
citations of
`docs/paper-gaps/cpsv16_active_physical_support_compression.tex` verbatim.

## What was checked

The in-tree call site,
`exists_etaLocalStructureData_supported_of_twoSidedPhysicalSlice` in
`TNLean/MPS/MPDO/PhysicalSectorActiveBond.lean`, uses the preferred declarations
directly. Its restricted factorization keeps an explicit type ascription; this
is the type-level behavior exposed by the retained
`factorizationForRestrictionData` compatibility declaration.

The relocated trace factorization applies `sum_mul_activeSectorFinEquiv`
directly. The deprecated `neighboringTraceFactorization` wrapper delegates to
that construction, while the old sector-correspondence-qualified name remains
available to downstream code.

Neither relocated name collides in the enclosing namespace, which was checked
against `compressedNeighboringOperator_trace` and the other
`*_neighboringTraceFactorization` declarations of the MPDO modules.

## Blueprint

`thm:mpdo_active_physical_sector_neighboring_positivity` in
`blueprint/src/chapter/ch21_mpdo_rfp_simple_local_structure_capstone.tex` uses
the preferred declarations. The deprecated structure and its former blueprint
qualified names remain valid for downstream users; the `\leanok` and the prose
are untouched.

`docs/paper-gaps/cpsv16_active_physical_support_compression.tex` cites the
preferred relocated trace-factorization name by `\leanid`.

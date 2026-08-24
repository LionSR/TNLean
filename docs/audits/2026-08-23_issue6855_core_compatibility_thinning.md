# Issue #6855: core compatibility thinning audit

This note records a TNLean-local reduction of the duplicate
`Kraus`/`MPSTensor` and bond-cast interfaces from the August 2026 structural
debt review.

## Blocking definitions

The following public `MPSTensor` names remain available, but their copied
definition bodies are replaced by abbreviations of the canonical QICLean
finite-family definitions:

| TNLean name | Canonical body |
|---|---|
| `MPSTensor.blockPhysDim` | `Kraus.blockPhysDim` |
| `MPSTensor.singleBlockEquiv` | `Kraus.singleBlockEquiv` |
| `MPSTensor.decodeBlock` | `Kraus.decodeBlock` |
| `MPSTensor.wordOfBlock` | `Kraus.wordOfBlock` |
| `MPSTensor.decodeBlockEquiv` | `Kraus.decodeBlockEquiv` |
| `MPSTensor.blockTensor` | `Kraus.blockTensor` |
| `MPSTensor.flattenBlockedWord` | `Kraus.flattenBlockedWord` |

The forwarding lemmas retain their TNLean names for compatibility, while only
the canonical `Kraus` copies carry the simplification attributes. The three
injectivity-predicate copies named by issue #6855 no longer occur on current
main: the QICLean extraction removed their former TNLean module and migrated
live consumers directly to the canonical predicates.

Replacing an opaque wrapper by an abbreviation changes which constant an
explicit unfolding or restricted simplification step must name. The necessary
proof repairs therefore name the canonical definitions directly. They are
confined to the blocking calculations in `Core/Blocking.lean`,
`Core/BlockingInfrastructure.lean`, and `Core/BlockingTransfer.lean`; the
canonical-form and example calculations in `CPSVBlocking.lean`, `Conjugation.lean`,
`CommonBlockedCyclicSectorFamily.lean`,
`FundamentalTheorem/SectorBNT/Blocking.lean`, `AKLTStringOrder.lean`, and
`Cluster.lean`; the MPDO and boundary calculations in
`BlockedBNTFusionIsometries.lean`, `FirstSiteBlocking.lean`,
`PhysicalBlocking.lean`, and `ExtendRight.lean`; the MPU calculations in
`BlockingRanks.lean`, `CanonicalForm.lean`, `SimpleBlocking.lean`,
`SourceURangeTransport.lean`, `SourceUReflectedKernel.lean`,
`TensorProduct.lean`, and `ThreeFormSpan.lean`; the periodic and symmetry
calculations in
`Periodic/Defs.lean`,
`Periodic/Overlap/NoSectorMatch.lean`,
`Periodic/Overlap/SectorMatch/Contraction.lean`,
`Periodic/Overlap/SectorOverlapTransport.lean`,
`Periodic/SectorContraction.lean`, and `Symmetry/Defs.lean`; and the encoded
word calculation in `Wielandt/RectangularSpan/Basic.lean`. No mathematical
statement changes in these consumers.

## Bond reindexing

`MPSTensor.reindex` is now the canonical equivalence for transport along an
equality of bond dimensions. The module also records its application,
word-evaluation, MPV, and gauge properties. The cast-to-reindex and application
lemmas replace four private cast calculations:

| Removed private declaration | Replacement |
|---|---|
| `MPSTensor.CPSVCanonicalFormData.mpsTensor_cast_apply` in `CanonicalFormEqualAmbient.lean` | `MPSTensor.cast_eq_reindex` and `MPSTensor.reindex_apply_eq_cast` |
| `MPSTensor.mpsTensor_cast_apply` in `FundamentalCoord.lean` | `MPSTensor.cast_eq_reindex` and `MPSTensor.reindex_apply_apply` |
| `MPSTensor.mpsTensor_cast_apply_matrix` in `PreparedReconstruction.lean` | `MPSTensor.cast_eq_reindex` and `MPSTensor.reindex_apply_eq_cast` |
| `MPOTensor.RetainedProductSpectralFamily.castTensor_apply` in `VerticalProductCornerComparison.lean` | `MPSTensor.cast_eq_reindex` and `MPSTensor.reindex_apply_eq_cast` |

The remaining differently named cast helpers in
`NormalizedGroupedSectorMaps.lean` and
`BNTAlgebraTensorClauseDirectSumUnitary.lean` have different dependent
contexts and are not claimed by this migration.

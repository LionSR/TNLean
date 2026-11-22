# Issue #6855: concept-level module splits

This note records the first reduction of the 900--1000-line warning band.  The
ten modules that were at or above 976 lines on 2026-08-23 were split at named
mathematical phases.  Each original module remains an importing facade, so its
former downstream import surface is preserved.

| Original module | Extracted module |
|---|---|
| `MPS/Operator/Simple/SimpleLocalStructure.lean` | `MPS/Operator/Simple/SimpleLocalInverseMaps.lean` |
| `MPS/MPDO/PhysicalSector/PhysicalSectorActiveRestriction.lean` | `MPS/MPDO/PhysicalSector/PhysicalSectorActiveCoordinates.lean` |
| `MPS/MPDO/CommutingForm/FourCycleMarkov.lean` | `MPS/MPDO/GSNNCHFourCycleMarkov/OverlappingLiftAlgebra.lean` |
| `MPS/Tensor/GroundSpace/BoundaryClosingStripping.lean` | `MPS/Tensor/GroundSpace/BoundaryClosingTraceReconstruction.lean` |
| `MPS/ParentHamiltonian/BlockGroundSpace/BoundaryMatrix/BlockIntersectionProperty.lean` | `MPS/ParentHamiltonian/BlockGroundSpace/BoundaryMatrix/BlockIntersectionBoundaryDecomposition.lean` |
| `MPS/Tensor/GroundSpace/UniqueGroundState.lean` | `MPS/Tensor/GroundSpace/PeriodicBoundaryReduction.lean` |
| `MPS/Tensor/GroundSpace/WrappingWindow.lean` | `MPS/Tensor/GroundSpace/WrappingWindowLastSiteFactorization.lean` |
| `PEPS/Injectivity/Normal/NormalEdgeBlockingTranslated.lean` | `PEPS/Injectivity/Normal/NormalEdgeBlockingTranslatedCoordinate.lean` |
| `PEPS/FundamentalTheorem/Injective/FundamentalTheorem.lean` | `PEPS/FundamentalTheorem/Injective/LocalGaugeExtraction.lean` |
| `PEPS/FundamentalTheorem/Normal/RegionInsertion/InsertedCoefficientExpansion.lean` | `PEPS/FundamentalTheorem/Normal/RegionInsertion/InsertedCoefficientExpansion.lean` |

The Four-Cycle split crosses one genuine proof boundary: six matrix lemmas used
by the later Markov argument can no longer remain file-private.  They are now
public under their existing names in `OverlappingLiftAlgebra.lean`:

- `Matrix.overlappingLifts_mul_eq_zero_of_middle_mul_eq_zero`;
- `Matrix.leftOverlappingLift_sum`;
- `Matrix.leftOverlappingLift_smul`;
- `Matrix.rightOverlappingLift_sum`;
- `Matrix.posSemidef_of_leftOverlappingLift_posSemidef`;
- `Matrix.posSemidef_of_rightOverlappingLift_posSemidef`.

This is a deliberate API expansion.  The lemmas express reusable algebraic and
positivity properties of overlapping lifts, and keeping their consumers in the
same file would leave the proposed split above the warning threshold.  No
existing public name, theorem statement, docstring, or Blueprint citation is
changed by the ten splits.

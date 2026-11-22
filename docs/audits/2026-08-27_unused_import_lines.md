# Unused import lines: 2026-08-27 sweep

This audit records a cross-cutting sweep of import lines that no identifier in
their file needed. No declaration was removed, so no blueprint `\lean{}` tag
moved and no compatibility alias question arises. Three surveyed batches are
folded together here because they were applied and verified as one root build.

Net delta of this sweep: −23 Lean lines (one of the twenty-four edits is a
one-for-one replacement, not a deletion).

A later cross-cutting pass added one further line to the table below, the
`QICLean.Kraus.MixedMap.Basic` import of `TNLean/MPS/MPDO/Purification/PureRFPSAL.lean`, bringing
the sweep to −24 Lean lines across twenty-five edits. That module keeps four
other TNLean importers, so the removal narrows one module's import closure
rather than dropping the mixed-map development from the build.

## Method, and the mistake the method has to avoid

An import line is a candidate when no identifier that the file elaborates is
supplied by that import's **exclusive cone** — the modules reachable from that
import and from no other import of the same file. The cone must be computed
over the whole import graph, Mathlib included, and must honour `public import`
under Lean's module system, because a re-exported module belongs to the cone of
whatever re-exports it.

A cone computed over the TNLean and QICLean sources alone truncates at the
Mathlib boundary and silently drops instances, notation, `simp` lemmas,
`to_additive` images, and `elab_as_elim` attributes that no named identifier in
the file mentions. That truncation is what produced the over-claim in the
original survey of this batch, and the corrected survey deferred five lines on
exactly that ground (below).

Even a correct cone is only a candidate generator. An import is proved dead by
a **root** `lake build`, never by a module-target build: a module target builds
the file's dependencies, and the effect of a missing import is felt in the
file's *importers*. Twenty-one of the forty-three lines attempted in this sweep
were proved live only by importers several modules downstream.

## Removed

### `TNLean.MPS.Tensor.Words.TracePairing`

| File | Line removed |
|---|---|
| `TNLean/MPS/Tensor/Words/TensorEquality.lean` | `import TNLean.Algebra.TracePairing` |
| `TNLean/MPS/Tensor/GroundSpace/Nonvanishing.lean` | `import TNLean.Algebra.TracePairing` |
| `TNLean/MPS/Operator/PhysicalSector/PhysicalSectorSupportRecurrence.lean` | `import TNLean.Algebra.TracePairing` |
| `TNLean/MPS/Operator/DensityOperator/RFPViaTS.lean` | `import TNLean.Algebra.TracePairing` |

The module was subsequently moved from `TNLean/Algebra/TracePairing.lean` to
`TNLean/MPS/Tensor/Words/TracePairing.lean`; `TNLean/MPS/Core.lean` now keeps it
root-reachable. `TNLean/MPS/Tensor/Gauge/FiniteLength.lean`,
`TNLean/MPS/Tensor/Words/LinearExtension.lean` and
`TNLean/MPS/CanonicalForm/BlockSeparation/DirectSumInput.lean` are genuine users of its
declarations.

### The QICLean cyclic-decomposition umbrella

| File | Change |
|---|---|
| `TNLean/MPS/Transfer/Irreducible/PeriodicBlocking.lean` | `QICLean.Channel.Peripheral.CyclicDecomposition` replaced by `QICLean.Algebra.Hermitian.CornerCompression` |
| `TNLean/MPS/CanonicalForm/Periodic/CyclicSectors/Basic.lean` | `QICLean.Channel.Peripheral.CyclicDecomposition` and `QICLean.Channel.Peripheral.Conjugation` removed |
| `TNLean/MPS/Transfer/Irreducible/Periodic.lean` | `QICLean.Channel.Peripheral.CyclicDecomposition` removed |
| `TNLean/MPS/Periodic/Symmetry/EqualCaseFTHyp.lean` | `QICLean.Channel.Peripheral.CyclicDecomposition` removed |
| `TNLean/MPS/CanonicalForm/NormalBlocks/TPGauge.lean` | `QICLean.Channel.Peripheral.CyclicDecomposition` removed |

**`TNLean/MPS/CanonicalForm/Periodic/CyclicSectors/Compression.lean` keeps its umbrella
import deliberately.** Nothing inside `Compression.lean` uses it, but it is the
only path by which `TNLean/MPS/CanonicalForm/Periodic/CyclicSectors/CornerBridge.lean`
(which imports `Compression` directly) reaches `PreservesCorner`,
`cornerRestriction`, `IsIrreducibleOnCorner`, `IsIrreducibleMap` and
`IsPrimitive.conj_iff_cross`, all used in its proofs, and the only path by which
`TNLean/MPS/CanonicalForm/Periodic/CyclicSectors/HLift.lean` reaches
`Kraus.fixed_eq_scalar_of_irreducible_unital`. A later sweep should not
re-propose it without first giving `CornerBridge.lean` and `HLift.lean` the
narrower imports they actually need — an explicitness fix that adds lines
rather than removing them.

The umbrella therefore stays reachable from TNLean; this sweep narrows its
importer set, it does not disconnect it.

### Further dead import lines

| File | Module dropped |
|---|---|
| `TNLean/MPS/Transfer/Irreducible/FixedPointProjection.lean` | `QICLean.Channel.Irreducible.Basic` |
| `TNLean/MPS/Examples/BondTwoSingleton/BondTwoSingletonPhysicalGauge.lean` | `TNLean.MPS.CanonicalForm.NormalBlocks.Blocking` |
| `TNLean/MPS/MPDO/PhysicalSector/NeighboringTraceObstruction.lean` | `QICLean.Algebra.Matrix.MatrixCyclicTracePower` |
| `TNLean/MPS/MPDO/Purification/PureRFPSAL.lean` | `QICLean.Kraus.MixedMap.Basic` |
| `TNLean/MPS/Examples/MPDOCounterexamples/Theorem49RepeatedCopyCounterexample.lean` | `TNLean.MPS.CanonicalForm.SimpleMPO.SimpleTensor` |
| `TNLean/MPS/Transfer/Spectrum/CastDecay.lean` | `TNLean.MPS.Transfer.Spectrum.TransferOperatorGapInjective` |
| `TNLean/MPS/ParentHamiltonian/BlockGroundSpace/BoundaryMatrix/BNTBlockDiagonalCrossing.lean` | `TNLean.MPS.ParentHamiltonian.BlockGroundSpace.BoundaryMatrix.BNTBlockDiagonalLastCrossing` |
| `TNLean/MPS/Transfer/Irreducible/Periodic.lean` | `TNLean.MPS.Transfer.Irreducible.PeriodicBlocking` |
| `TNLean/MPS/CanonicalForm/Periodic/CyclicSectors/StateVectorDecomposition.lean` | `TNLean.MPS.Tensor.Words.CyclicTrace` |
| `TNLean/PEPS/FundamentalTheorem/Normal/RegionInsertion/ThreeBlockTransfer.lean` | `TNLean.PEPS.RegionBlock.ThreeBlockReconcile` |
| `TNLean/PEPS/Injectivity/Region/DisjointUnionSetup.lean` | `TNLean.PEPS.FundamentalTheorem.Normal.RegionInsertion.BlockRangeCoincidence` |
| `TNLean/PEPS/FundamentalTheorem/Torus/TorusGaugedWeightCovariance.lean` | `TNLean.PEPS.FundamentalTheorem.Normal.RegionInsertion.ProportionalityFromAbsorbed` |
| `TNLean/MPS/CanonicalForm/BlockFamily.lean` | `TNLean.MPS.Transfer.Spectrum.Proportional` |
| `TNLean/MPS/Transfer/Primitivity/Bounds.lean` | `TNLean.MPS.Transfer.Primitivity.Bounds` |
| `TNLean/MPS/Transfer/Primitivity/RectangularSpan.lean` | `QICLean.Kraus.Wielandt.RankOne.Construction` |

`TNLean/MPS/Transfer/Spectrum/CastDecay.lean` deserves a word. Its
`TNLean.MPS.Transfer.Spectrum.TransferOperatorGapInjective` line was introduced one commit
earlier by PR #7211 as the migration target for the deleted
`Spectral.MPVOverlapDecay` waypoint (see
`docs/audits/2026-08-26_spectral_import_waypoint_retirement.md`). It is removed
here because the migration target turned out to be redundant at that particular
consumer, which already reaches everything it needs through
`TNLean.MPS.Transfer.Spectrum.TransferOperatorGapNT` — not because the migration was wrong.

## Proved live, and retained

Twenty-one candidate lines were restored after a root build named the
identifier that the import supplies. They are recorded here so that a later
sweep does not re-propose them.

| File | Import retained | Identifier that forced it | Consumer |
|---|---|---|---|
| `TNLean/MPS/Tensor/GroundSpace/IntersectionProperty.lean` | `TNLean.MPS.Tensor.Words.TracePairing` | `ker_bot_of_range_le` | `TNLean/PEPS/Tensor/Cycle/CycleMPSWordTransport.lean:122` |
| `TNLean/MPS/CanonicalForm/DiagonalRestrictionCounterexample.lean` | `TNLean.MPS.Tensor.Words.TracePairing` | `Matrix.trace_mul_right_eq_zero_iff` | same file, line 160 |
| `TNLean/MPS/Tensor/DirectSum/MultiBlock.lean` | `QICLean.Algebra.Matrix.MatrixReindex` | `Matrix.trace_reindex` | `TNLean/MPS/Core/BlockTriangularTrace.lean`, `TNLean/MPS/Tensor/DirectSum/BlockAssembly.lean` |
| `TNLean/Algebra/CommutingProjectionProduct.lean` | `QICLean.Algebra.Kronecker.KroneckerFactorPositivity` | `Matrix.trace_piProduct` | `TNLean/MPS/ParentHamiltonian/Commuting/SectorGraph/BeigiSectorGraph.lean:457` |
| `TNLean/MPS/Tensor/DirectSum/SectorBNT.lean` | `TNLean.MPS.Tensor.DirectSum.SectorWeightComparison` | `Matrix.charpoly_eq_of_forall_trace_pow_eq` | `TNLean/MPS/CanonicalForm/BNTPresentation/PreparedBlocksNormalized.lean:60` |
| `TNLean/MPS/Tensor/DirectSum/SectorWeightComparison.lean` | `QICLean.Algebra.Polynomial.ScalarPowerSumIdentity` | `Matrix.sum_pow_eq_implies_card_eq_and_multiset_eq_of_le_max_card` | `TNLean/MPS/MPDO/Coefficients/BNTMultiplicityNormalization.lean:150`, `TNLean/MPS/FundamentalTheorem/Sectors/WeightEquiv.lean:129` |
| `TNLean/MPS/MPDO/BNTSectors/BNTSectorAreaLaw.lean` | `TNLean.MPS.CanonicalForm.SimpleMPO.PhysicalSupportRestriction` | `commonWeightAbsorbedBasisMPOTensor_isInjective` | same file, line 443 |
| `TNLean/MPS/MPDO/CyclicActiveSector/CyclicActiveRetainedCoordinates.lean` | `TNLean.MPS.MPDO.Entropy.SourceZCLMarginal` | `reducedBlockState_add_three_eq_succ_of_isSourceZCL` | `TNLean/MPS/MPDO/CyclicActiveSector/CyclicActiveFourthRegionContraction.lean:652` |
| `TNLean/MPS/MPDO/Fusion/VerticalProductReconstruction.lean` | `TNLean.MPS.MPDO.Vertical.HorizontalBlocking` | `blockTwo` | `TNLean/MPS/MPDO/Fusion/VerticalProductRetainedBlocks.lean:180` |
| `TNLean/MPS/MPDO/Fusion/VerticalProductReconstruction.lean` | `TNLean.MPS.CanonicalForm.BNT.Transport` | `IsCPSVBasisOfNormalTensors.of_sameMPV₂Pos` | `TNLean/MPS/MPDO/Fusion/VerticalProductSpectralFamily.lean:494` |
| `TNLean/MPS/MPDO/Fusion/VerticalProductReconstruction.lean` | `TNLean.MPS.MPDO.Vertical.VerticalBNTConstruction` | `sameMPV₂Pos_toTensorFromBlocks_of_reconstruction` | `TNLean/MPS/MPDO/Fusion/VerticalProductSpectralFamily.lean:439` |
| `TNLean/MPS/ParentHamiltonian/BlockGroundSpace/BoundaryMatrix/BlockIntersectionBoundaryDecomposition.lean` | `TNLean.MPS.ParentHamiltonian.BlockGroundSpace.BoundaryMatrix.BoundaryMatrixIdentities` | `pgvwc07_boundary_matrix_identities_of_compatibility` | `TNLean/MPS/ParentHamiltonian/BlockGroundSpace/BoundaryMatrix/BlockIntersectionProperty.lean:285` |
| `TNLean/MPS/Tensor/GroundSpace/BoundaryClosingTraceReconstruction.lean` | `TNLean.MPS.Tensor.GroundSpace.BoundaryMatrixBlock` | `boundary_matrix_commutes_of_isNBlkInjective_of_block_matEq` | `TNLean/MPS/Tensor/GroundSpace/BoundaryClosingStripping.lean:280` |
| `TNLean/MPS/Tensor/GroundSpace/WrappingWindowLastSiteFactorization.lean` | `TNLean.MPS.Tensor.GroundSpace.BlockStrip` | `commutes_all_of_commutes_long_words_of_isNBlkInjective` | `TNLean/MPS/Tensor/GroundSpace/WrappingWindow.lean:635` |
| `TNLean/MPS/CanonicalForm/Periodic/CyclicSectors/ProjectionOrtho.lean` | `TNLean.MPS.Transfer.Irreducible.PeriodicBlocking` | `orbitSumProjection` | `TNLean/MPS/CanonicalForm/Periodic/CyclicSectors/OrbitSum.lean:46` |
| `TNLean/MPS/Tensor/DirectSum/InvariantSubspaceDecomp.lean` | `TNLean.Algebra.ProjectionTriangularTrace` | `Kraus.diagPart`, `sameMPV_diagPart_of_lowerZero` | `TNLean/MPS/Tensor/DirectSum/InvariantSubspaceDecomp.lean:171` |
| `TNLean/PEPS/FundamentalTheorem/Injective/LocalGaugeExtraction.lean` | `TNLean.PEPS.FundamentalTheorem.Injective.TensorFactorScalar` | `piProduct_forms_scalar` | `TNLean/PEPS/FundamentalTheorem/Injective/Uniqueness.lean:382` |
| `TNLean/PEPS/Injectivity/Region/DisjointUnionSetup.lean` | `TNLean.PEPS.RegionBlock.Recovery11` | `regionInteriorBondProd`, `regionFiber_card` | same file, line 340 |
| `TNLean/PEPS/Tensor/Region/VertexComplement.lean` | `TNLean.PEPS.Tensor.Network.FiniteKernelDescent` | `FiniteRegionKernelDescent` | `TNLean/PEPS/Injectivity/Region/RegionKernelDescent.lean:549` |
| `TNLean/MPS/Tensor/Words/WordSpan.lean` | `QICLean.Kraus.Wielandt.SpanGrowth.VectorToMatrixSpan` | `Kraus.wordSpan_top_of_mul` | `TNLean/MPS/Tensor/GroundSpace/WrappingWindow.lean:694` |
| `TNLean/MPS/Tensor/Words/WordSpan.lean` | `TNLean.MPS.Tensor.Words.WordSpan` | `wordSpan_eq_top_iff_isNBlkInjective` | `TNLean/MPS/Transfer/Primitivity/RectangularSpan.lean:139` |

The pattern in that table is worth naming: most of these imports are dead
*inside* their own file and live only through re-export. Sixteen of the
twenty-one were forced by a consumer in a different module. An import survey
that stops at the file boundary will keep proposing them.

## Deferred lines cleared in follow-up #7228

The five lines deferred by the original static survey were each removed and
checked in the follow-up batch. Three remain deleted. The
`CanonicalFormSepAux.lean` line was restored when its changed-module build named
the supplied identifier; the `TransferPeripheral.lean` line was restored when
the root build exposed its downstream use in `NormalizedSelfOverlap.lean`.
The final root build succeeds with those two imports restored.

| File | Module dropped | Local outcome |
|---|---|---|
| `TNLean/PEPS/FundamentalTheorem/Injective/GaugeAction.lean` | `TNLean.PEPS.FundamentalTheorem.Injective.EdgeGaugeFamily` | changed module builds without the line |
| `TNLean/MPS/Tensor/GroundSpace/BoundaryOverlap.lean` | `TNLean.MPS.Tensor.GroundSpace.BlockStrip` | changed module builds without the line |
| `TNLean/MPS/Tensor/GroundSpace/BlockStrip.lean` | `TNLean.MPS.Tensor.Gauge.FiniteLength` | changed module builds without the line |
| `TNLean/MPS/Transfer/Irreducible/TransferPeripheral.lean` | `QICLean.Channel.Peripheral.CyclicGroupKraus` | restored: the root build named `Kraus.peripheralEigenvalues_eq_range_primitiveRoot` in `TNLean/MPS/CanonicalForm/Periodic/Overlap/NormalizedSelfOverlap.lean` |
| `TNLean/MPS/CanonicalForm/BlockFamily.lean` | `TNLean.MPS.Transfer.Spectrum.PrimitiveOverlap` | restored: the build named `MPSTensor.overlap_tendsto_one_of_peripheralPrimitive_of_irreducible` at lines 230 and 328 |

## Already absent

Four lines named by the survey no longer existed in the tree and needed no
edit: `TNLean/PEPS/Injectivity/Region/CycleMPSChainArc.lean` and
`TNLean/PEPS/Injectivity/Region/CycleMPSInjectivity.lean` (both `TNLean.Algebra.TracePairing`),
and the `TNLean/MPS/MPDO/Vertical/CyclicProjector.lean`,
`TNLean/MPS/Tensor/GroundSpace/PeriodicBoundaryReduction.lean` (four lines),
`TNLean/MPS/CanonicalForm/RenormalizationFixedPoint/BNTOrthogonality.lean`, `TNLean/MPS/ParentHamiltonian/Commuting/SectorGraph/BeigiSectorGraph.lean`
and `TNLean/PEPS/RegionScalarCondition.lean` entries.

`docs/audits/lean_spaghetti_canonicalform_ft.md:756` is directional support
only: it names `CyclicSectors.lean`, which is now the generated per-directory
aggregator rather than the module it described.

## Two further lines, from the cross-cutting duplication pass

Two more import lines were cleared by the cross-cutting duplication pass of the
same day and are folded in here rather than given a note of their own.

| File | Module dropped | Why it went dead |
|---|---|---|
| `TNLean/MPS/CanonicalForm/Periodic/CyclicSectors/CyclicSectorDecomposition.lean` | `QICLean.Channel.Schwarz.MultiplicativeDomainFull` | the Kadison–Schwarz argument moved to `TNLean/MPS/CanonicalForm/Periodic/CyclicSectors/HLift.lean`, leaving no multiplicative-domain name in the file; the `open KadisonSchwarz` line went with it (see `docs/audits/2026-08-27_cross_cutting_private_duplication.md`) |
| `TNLean/MPS/CanonicalForm/NormalBlocks/NormalCanonicalForm.lean` | `TNLean.MPS.CanonicalForm.NormalBlocks.IrreducibleDecomposition` | no identifier the file elaborates comes from that import's exclusive cone |

The second row is import hygiene plus a shorter critical path for that one
module — it no longer waits on a thirty-module, 6,879-line upstream cone — and
**not** a reduction in total build work. `NormalReduction.lean` still reaches
`Existence.lean` through `NormalReduction/TPGauge.lean`, and `CanonicalForm.lean`
imports it directly, so the cone is still compiled for every consumer of the
aggregator. No declaration moved:
`MPSTensor.exists_normalCanonicalForm_of_primitive_blockDecomp` keeps its
Blueprint tag and its paper-gap reference.

## Verification

- `lake build` completes successfully at the repository root with the package
  lean options.
- `python3 scripts/check_forbidden_lean_tokens.py` is clean.
- `python3 scripts/check_numbered_lean_files.py`,
  `python3 scripts/check_oversized_lean_files.py` and
  `python3 scripts/generate_import_aggregators.py --check` pass; no file was
  deleted, so no aggregator changed.

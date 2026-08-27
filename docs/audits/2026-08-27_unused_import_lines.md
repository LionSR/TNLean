# Unused import lines: 2026-08-27 sweep

This audit records a cross-cutting sweep of import lines that no identifier in
their file needed. No declaration was removed, so no blueprint `\lean{}` tag
moved and no compatibility alias question arises. Three surveyed batches are
folded together here because they were applied and verified as one root build.

Net delta of this sweep: −23 Lean lines (one of the twenty-four edits is a
one-for-one replacement, not a deletion).

A later cross-cutting pass added one further line to the table below, the
`QICLean.Kraus.MixedMap` import of `TNLean/MPS/MPDO/PureRFPSAL.lean`, bringing
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

### `TNLean.Algebra.TracePairing`

| File | Line removed |
|---|---|
| `TNLean/MPS/Chain/TensorEquality.lean` | `import TNLean.Algebra.TracePairing` |
| `TNLean/MPS/ParentHamiltonian/Nonvanishing.lean` | `import TNLean.Algebra.TracePairing` |
| `TNLean/MPS/MPDO/PhysicalSectorSupportRecurrence.lean` | `import TNLean.Algebra.TracePairing` |
| `TNLean/MPS/MPDO/RFPViaTS.lean` | `import TNLean.Algebra.TracePairing` |

`TNLean/Algebra.lean` keeps `TNLean.Algebra.TracePairing` root-reachable, and
`TNLean/MPS/FundamentalTheorem/FiniteLength.lean`,
`TNLean/MPS/Structure/LinearExtension.lean` and
`TNLean/MPS/MPDO/BiCFDerivation/DirectSumInput.lean` are genuine users of its
declarations.

### The QICLean cyclic-decomposition umbrella

| File | Change |
|---|---|
| `TNLean/MPS/Irreducible/PeriodicBlocking.lean` | `QICLean.Channel.Peripheral.CyclicDecomposition` replaced by `QICLean.Algebra.CornerCompression` |
| `TNLean/MPS/CanonicalForm/CyclicSectors/Basic.lean` | `QICLean.Channel.Peripheral.CyclicDecomposition` and `QICLean.Channel.Peripheral.Conjugation` removed |
| `TNLean/MPS/Periodic/Defs.lean` | `QICLean.Channel.Peripheral.CyclicDecomposition` removed |
| `TNLean/MPS/Periodic/Symmetry/EqualCaseFTHyp.lean` | `QICLean.Channel.Peripheral.CyclicDecomposition` removed |
| `TNLean/MPS/CanonicalForm/SectorComparison/TPPrimitiveReduction.lean` | `QICLean.Channel.Peripheral.CyclicDecomposition` removed |

**`TNLean/MPS/CanonicalForm/CyclicSectors/Compression.lean` keeps its umbrella
import deliberately.** Nothing inside `Compression.lean` uses it, but it is the
only path by which `TNLean/MPS/CanonicalForm/CyclicSectors/CornerBridge.lean`
(which imports `Compression` directly) reaches `PreservesCorner`,
`cornerRestriction`, `IsIrreducibleOnCorner`, `IsIrreducibleMap` and
`IsPrimitive.conj_iff_cross`, all used in its proofs, and the only path by which
`TNLean/MPS/Periodic/SectorIrreducibility/HLift.lean` reaches
`Kraus.fixed_eq_scalar_of_irreducible_unital`. A later sweep should not
re-propose it without first giving `CornerBridge.lean` and `HLift.lean` the
narrower imports they actually need — an explicitness fix that adds lines
rather than removing them.

The umbrella therefore stays reachable from TNLean; this sweep narrows its
importer set, it does not disconnect it.

### Further dead import lines

| File | Module dropped |
|---|---|
| `TNLean/MPS/Irreducible/FixedPointProjection.lean` | `QICLean.Channel.Irreducible.Basic` |
| `TNLean/MPS/MPDO/BondTwoSingletonPhysicalGauge.lean` | `TNLean.MPS.CanonicalForm.CPSVBlocking` |
| `TNLean/MPS/MPDO/NeighboringTraceObstruction.lean` | `QICLean.Algebra.MatrixCyclicTracePower` |
| `TNLean/MPS/MPDO/PureRFPSAL.lean` | `QICLean.Kraus.MixedMap` |
| `TNLean/MPS/MPDO/Theorem49RepeatedCopyCounterexample.lean` | `TNLean.MPS.MPDO.SimpleTensor` |
| `TNLean/MPS/Overlap/CastDecay.lean` | `TNLean.Spectral.TransferOperatorGapInjective` |
| `TNLean/MPS/ParentHamiltonian/BNTBlockDiagonalCrossing.lean` | `TNLean.MPS.ParentHamiltonian.BNTBlockDiagonalLastCrossing` |
| `TNLean/MPS/Periodic/Defs.lean` | `TNLean.MPS.Irreducible.PeriodicBlocking` |
| `TNLean/MPS/Periodic/StateVectorDecomposition.lean` | `TNLean.MPS.Core.CyclicTrace` |
| `TNLean/PEPS/RegionBlock/ThreeBlockTransfer.lean` | `TNLean.PEPS.RegionBlock.ThreeBlockReconcile` |
| `TNLean/PEPS/RegionBlock/UnionInjectivityGeneral.lean` | `TNLean.PEPS.RegionBlock.BlockRangeCoincidence` |
| `TNLean/PEPS/TorusGaugedWeightCovariance.lean` | `TNLean.PEPS.RegionBlock.ProportionalityFromAbsorbed` |
| `TNLean/PiAlgebra/CanonicalFormSepAux.lean` | `TNLean.MPS.FundamentalTheorem.Proportional` |
| `TNLean/Wielandt/Inequality/Bounds.lean` | `TNLean.Wielandt.Inequality.EigenvectorSpreading` |
| `TNLean/Wielandt/RectangularSpan/Basic.lean` | `QICLean.Kraus.Wielandt.RankOne.Construction` |

`TNLean/MPS/Overlap/CastDecay.lean` deserves a word. Its
`TNLean.Spectral.TransferOperatorGapInjective` line was introduced one commit
earlier by PR #7211 as the migration target for the deleted
`Spectral.MPVOverlapDecay` waypoint (see
`docs/audits/2026-08-26_spectral_import_waypoint_retirement.md`). It is removed
here because the migration target turned out to be redundant at that particular
consumer, which already reaches everything it needs through
`TNLean.Spectral.TransferOperatorGapNT` — not because the migration was wrong.

## Proved live, and retained

Twenty-one candidate lines were restored after a root build named the
identifier that the import supplies. They are recorded here so that a later
sweep does not re-propose them.

| File | Import retained | Identifier that forced it | Consumer |
|---|---|---|---|
| `TNLean/MPS/ParentHamiltonian/IntersectionProperty.lean` | `TNLean.Algebra.TracePairing` | `ker_bot_of_range_le` | `TNLean/PEPS/CycleMPSWordTransport.lean:122` |
| `TNLean/MPS/MPDO/BiCFDerivation/DiagonalRestrictionCounterexample.lean` | `TNLean.Algebra.TracePairing` | `Matrix.trace_mul_right_eq_zero_iff` | same file, line 160 |
| `TNLean/MPS/Core/MultiBlock.lean` | `QICLean.Algebra.TraceReindex` | `Matrix.trace_reindex` | `TNLean/Algebra/BlockTriangularTrace.lean`, `TNLean/MPS/SharedInfra/BlockAssembly.lean` |
| `TNLean/Algebra/CommutingProjectionProduct.lean` | `QICLean.Algebra.PiProductTrace` | `Matrix.trace_piProduct` | `TNLean/MPS/RFP/BeigiSectorGraph.lean:457` |
| `TNLean/MPS/FundamentalTheorem/SectorBNT/Basic.lean` | `TNLean.MPS.FundamentalTheorem.SectorWeightComparison` | `Matrix.charpoly_eq_of_forall_trace_pow_eq` | `TNLean/MPS/FundamentalTheorem/SectorBNT/SupplierNormalized.lean:60` |
| `TNLean/MPS/FundamentalTheorem/SectorWeightComparison.lean` | `QICLean.Algebra.ScalarPowerSumIdentity` | `Matrix.sum_pow_eq_implies_card_eq_and_multiset_eq_of_le_max_card` | `TNLean/MPS/MPDO/BNTMultiplicityNormalization.lean:150`, `TNLean/MPS/FundamentalTheorem/SectorBNT/WeightEquiv.lean:129` |
| `TNLean/MPS/MPDO/BNTSectorAreaLaw.lean` | `TNLean.MPS.MPDO.PhysicalSupportRestriction` | `commonWeightAbsorbedBasisMPOTensor_isInjective` | same file, line 443 |
| `TNLean/MPS/MPDO/CyclicActiveRetainedCoordinates.lean` | `TNLean.MPS.MPDO.SourceZCLMarginal` | `reducedBlockState_add_three_eq_succ_of_isSourceZCL` | `TNLean/MPS/MPDO/CyclicActiveFourthRegionContraction.lean:652` |
| `TNLean/MPS/MPDO/VerticalProductReconstruction.lean` | `TNLean.MPS.MPDO.HorizontalBlocking` | `blockTwo` | `TNLean/MPS/MPDO/VerticalProductRetainedBlocks.lean:180` |
| `TNLean/MPS/MPDO/VerticalProductReconstruction.lean` | `TNLean.MPS.CanonicalForm.BNTTransport` | `IsCPSVBasisOfNormalTensors.of_sameMPV₂Pos` | `TNLean/MPS/MPDO/VerticalProductSpectralFamily.lean:494` |
| `TNLean/MPS/MPDO/VerticalProductReconstruction.lean` | `TNLean.MPS.MPDO.VerticalBNTConstruction` | `sameMPV₂Pos_toTensorFromBlocks_of_reconstruction` | `TNLean/MPS/MPDO/VerticalProductSpectralFamily.lean:439` |
| `TNLean/MPS/ParentHamiltonian/BlockIntersectionBoundaryDecomposition.lean` | `TNLean.MPS.ParentHamiltonian.BoundaryMatrixIdentities` | `pgvwc07_boundary_matrix_identities_of_compatibility` | `TNLean/MPS/ParentHamiltonian/BlockIntersectionProperty.lean:285` |
| `TNLean/MPS/ParentHamiltonian/BoundaryClosingTraceReconstruction.lean` | `TNLean.MPS.ParentHamiltonian.BoundaryMatrixBlock` | `boundary_matrix_commutes_of_isNBlkInjective_of_block_matEq` | `TNLean/MPS/ParentHamiltonian/BoundaryClosingStripping.lean:280` |
| `TNLean/MPS/ParentHamiltonian/WrappingWindowLastSiteFactorization.lean` | `TNLean.MPS.ParentHamiltonian.BlockStrip` | `commutes_all_of_commutes_long_words_of_isNBlkInjective` | `TNLean/MPS/ParentHamiltonian/WrappingWindow.lean:635` |
| `TNLean/MPS/Periodic/SectorIrreducibility/ProjectionOrtho.lean` | `TNLean.MPS.Irreducible.PeriodicBlocking` | `orbitSumProjection` | `TNLean/MPS/Periodic/SectorIrreducibility/OrbitSum.lean:46` |
| `TNLean/MPS/Structure/InvariantSubspaceDecomp/Basic.lean` | `TNLean.Algebra.ProjectionTriangularTrace` | `Kraus.diagPart`, `sameMPV_diagPart_of_lowerZero` | `TNLean/MPS/Structure/InvariantSubspaceDecomp.lean:171` |
| `TNLean/PEPS/FundamentalTheorem/LocalGaugeExtraction.lean` | `TNLean.PEPS.TensorFactorScalar` | `piProduct_forms_scalar` | `TNLean/PEPS/FundamentalTheorem/Uniqueness.lean:382` |
| `TNLean/PEPS/RegionBlock/UnionInjectivityGeneral.lean` | `TNLean.PEPS.RegionBlock.Recovery11` | `regionInteriorBondProd`, `regionFiber_card` | same file, line 340 |
| `TNLean/PEPS/VertexComplement/Basic.lean` | `TNLean.PEPS.FiniteKernelDescent` | `FiniteRegionKernelDescent` | `TNLean/PEPS/RegionBlock/KernelDescent.lean:549` |
| `TNLean/Wielandt/SpanGrowth/VectorToMatrixSpan.lean` | `QICLean.Kraus.Wielandt.SpanGrowth.VectorToMatrixSpan` | `Kraus.wordSpan_top_of_mul` | `TNLean/MPS/ParentHamiltonian/WrappingWindow.lean:694` |
| `TNLean/Wielandt/SpanGrowth/VectorToMatrixSpan.lean` | `TNLean.Wielandt.SpanGrowth.EigenvectorSpreading` | `wordSpan_eq_top_iff_isNBlkInjective` | `TNLean/Wielandt/RectangularSpan/Basic.lean:139` |

The pattern in that table is worth naming: most of these imports are dead
*inside* their own file and live only through re-export. Sixteen of the
twenty-one were forced by a consumer in a different module. An import survey
that stops at the file boundary will keep proposing them.

## Deferred, not cleared

Five further lines were carried by the survey but are deliberately untouched
here. Their exclusive cones do contain Mathlib instance, `simp`, `to_additive`
or `elab_as_elim` content, so no static argument settles them and each needs
its own build:

- `TNLean/PEPS/FundamentalTheorem/GaugeAction.lean:8`
- `TNLean/MPS/ParentHamiltonian/BoundaryOverlap.lean:6`
- `TNLean/MPS/ParentHamiltonian/BlockStrip.lean:8`
- `TNLean/MPS/Core/TransferPeripheral.lean:7`
- `TNLean/PiAlgebra/CanonicalFormSepAux.lean:13`

## Already absent

Four lines named by the survey no longer existed in the tree and needed no
edit: `TNLean/PEPS/CycleMPSChainArc.lean` and
`TNLean/PEPS/CycleMPSInjectivity.lean` (both `TNLean.Algebra.TracePairing`),
and the `TNLean/MPS/MPDO/CyclicProjector.lean`,
`TNLean/MPS/ParentHamiltonian/PeriodicBoundaryReduction.lean` (four lines),
`TNLean/MPS/RFP/BNTOrthogonality.lean`, `TNLean/MPS/RFP/BeigiSectorGraph.lean`
and `TNLean/PEPS/RegionScalarCondition.lean` entries.

`docs/audits/lean_spaghetti_canonicalform_ft.md:756` is directional support
only: it names `CyclicSectors.lean`, which is now the generated per-directory
aggregator rather than the module it described.

## Two further lines, from the cross-cutting duplication pass

Two more import lines were cleared by the cross-cutting duplication pass of the
same day and are folded in here rather than given a note of their own.

| File | Module dropped | Why it went dead |
|---|---|---|
| `TNLean/MPS/CanonicalForm/SectorComparison/CyclicSectorDecomposition.lean` | `QICLean.Channel.Schwarz.MultiplicativeDomainFull` | the Kadison–Schwarz argument moved to `TNLean/MPS/Periodic/SectorIrreducibility/HLift.lean`, leaving no multiplicative-domain name in the file; the `open KadisonSchwarz` line went with it (see `docs/audits/2026-08-27_cross_cutting_private_duplication.md`) |
| `TNLean/MPS/CanonicalForm/NormalReduction/Main.lean` | `TNLean.MPS.CanonicalForm.Existence` | no identifier the file elaborates comes from that import's exclusive cone |

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

# Modular Split Plan
# Goal: Split 4 god files into organic TN library layers
# Each agent: read this, do your split, check the box, lake build, report.

## Execution Order (sequential, lake build after each)

### Split 1: PositiveMapSpectral.lean (705 lines) → 3 new + 1 re-export

**New files to create:**

1. **MPSLean/MPS/PositiveMap.lean** (~282 lines)
   - Content: section PositiveMap (IsPositiveMap, IsTracePreservingMap, IsChannel, map_isHermitian) + section DensityMatrices (densityMatrices, all private helpers, compactness/convexity/nonempty) + section ChannelPreserves (map_densityMatrices)
   - Imports: same as original PositiveMapSpectral.lean (MPSLean.MPS.CPPrimitive + all Mathlib imports)
   - This is lines 1-282 of the original

2. **MPSLean/MPS/CesaroFixedPoint.lean** (~162 lines)
   - Content: section FixedPointDecomposition (posSemidef_parts_of_hermitian_fixedPoint — has sorry) + section CesaroMean (cesaroMean, cesaroMean_telescope, exists_posSemidef_fixedPoint)
   - Imports: MPSLean.MPS.PositiveMap
   - This is lines 284-446 of the original

3. **MPSLean/MPS/KadisonSchwarz.lean** (~243 lines)
   - Content: section KadisonSchwarz (krausMap, krausAdjointMap, IsUnitalKraus, IsTPKraus, kadison_schwarz all variants, hilbertSchmidt_contraction all variants) + section TransferMap (transferMap_isChannel)
   - Imports: MPSLean.MPS.PositiveMap (for IsChannel, IsPositiveMap), MPSLean.MPS.Transfer (for MPSTensor.transferMap)
   - This is lines 448-691 of the original
   - NOTE: Does NOT depend on CesaroFixedPoint

4. **MPSLean/MPS/PositiveMapSpectral.lean** → thin re-export:
   ```
   import MPSLean.MPS.PositiveMap
   import MPSLean.MPS.KadisonSchwarz
   import MPSLean.MPS.CesaroFixedPoint
   ```
   Plus the trailing comment from lines 693-705.

**Downstream check:** QuantumPerronFrobenius.lean imports PositiveMapSpectral → works unchanged via re-export.

### Split 2: QuantumPerronFrobenius.lean (885 lines) → 2 new + 1 slimmed

1. **MPSLean/MPS/QPF/PosDef.lean** (~430 lines)
   - Content: section PosDef — all private helpers (eig_conj_mul, eig_mul_conj, spectral_decomp_eq, dotProduct_mulVec_conjTranspose, mulVec_eq_zero_of_quadForm_eq_zero, ker_invariant_under_adjoint, ker_contains_all_of_span) + posSemidef_fixedPoint_isPosDef + posSemidef_fixedPoint_isPosDef_of_irreducible
   - Imports: MPSLean.MPS.PositiveMapSpectral, Mathlib.Tactic.NoncommRing

2. **MPSLean/MPS/QPF/Uniqueness.lean** (~335 lines)
   - Content: section Uniqueness — all private helpers (eigenvectorUnitary_isUnit', sqrtΛ', sqrtInvΛ', etc.) + exists_critical_scalar + posSemidef_fixedPoint_unique
   - Imports: MPSLean.MPS.QPF.PosDef

3. **MPSLean/MPS/QuantumPerronFrobenius.lean** → slim to ~120 lines:
   - Re-exports QPF.PosDef and QPF.Uniqueness
   - Keeps: section Existence (exists_posSemidef_fixedPoint) + section Assembly (quantum_perron_frobenius, injective_transfer_unique_fixed_point')

**Downstream check:** TransferSpectral.lean, Scratch.lean import QPF → works via re-export.

### Split 3: TransferSpectral.lean (848 lines) → 4 new + 1 re-export

1. **MPSLean/MPS/MixedTransfer.lean** (~170 lines)
   - Content: sections MixedTransfer + IteratedTransfer (mixedTransferMap, apply, smul, self, pow_apply, trace_identity, mpv_inner_product_via_trace)
   - Imports: MPSLean.MPS.Defs, Mathlib basics (BigOperators, Matrix)

2. **MPSLean/MPS/FrobeniusNorm.lean** (~230 lines)
   - Content: NormedRing/NormedAlgebra instances, transferMatrix def, frobSq and all helpers, word_conjTranspose_mul_sum, toES embedding, hs_contraction_mixedTransfer
   - Imports: MPSLean.MPS.MixedTransfer, MPSLean.MPS.KadisonSchwarz (for hilbertSchmidt_contraction), + Mathlib norm/analysis imports

3. **MPSLean/MPS/SpectralGap.lean** (~200 lines)
   - Content: eigenvalue_norm_le_one, spectralRadius_mixedTransfer_le_one, modulus_one_eigenvalue_implies_gauge (axiom), spectralRadius_mixedTransfer_lt_one, pow_tendsto_zero_of_spectralRadius_lt_one, mixedTransfer_pow_tendsto_zero
   - Imports: MPSLean.MPS.FrobeniusNorm, Mathlib Gelfand/eigenspace imports

4. **MPSLean/MPS/CrossCorrelation.lean** (~80 lines)
   - Content: section BlockSeparation: cross_correlation_tendsto_zero, self_correlation_persists, block_separation_principle
   - Imports: MPSLean.MPS.SpectralGap, MPSLean.MPS.MixedTransfer

5. **MPSLean/MPS/TransferSpectral.lean** → thin re-export

### Split 4: PiAlgebraExtension.lean (648 lines) → 3 new + 1 re-export

1. **MPSLean/MPS/PiAlgebra.lean** (~320 lines)
   - Content: sections SummedTraces + PiAlgEquivConstruction + Decomposition + PiTraceNondeg + PiGramMap (lines 1-320)
   - Imports: MPSLean.MPS.BlockPermutationMPS, MPSLean.MPS.LinearExtension, MPSLean.MPS.MultiBlock, Mathlib.LinearAlgebra.Pi, Mathlib.LinearAlgebra.Matrix.Trace

2. **MPSLean/MPS/MultiBlockComplete.lean** (~200 lines)
   - Content: sections FullMultiBlock + SingleBlockSeparation + EndToEnd + Equivalence (lines 323-530)
   - Imports: MPSLean.MPS.PiAlgebra, MPSLean.MPS.BasisNormal, MPSLean.MPS.FundamentalTheoremMulti

3. **MPSLean/MPS/BlockSeparation.lean** (~120 lines)
   - Content: section BlockSeparation: evalWord helpers, block_powsum_separation (sorry), sameMPV₂_implies_perBlock_sameMPV, fundamentalTheorem_multiBlock_complete (lines 531-648)
   - Imports: MPSLean.MPS.MultiBlockComplete

4. **MPSLean/MPS/PiAlgebraExtension.lean** → thin re-export

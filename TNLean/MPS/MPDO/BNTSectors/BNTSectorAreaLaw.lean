/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.Combinatorics.FinSum
import TNLean.MPS.MPDO.BNTSectors.BNTSectorAnalyticProperties
import TNLean.MPS.MPDO.Entropy.LocalOrthogonalSumAreaLaw
import TNLean.MPS.CanonicalForm.SimpleMPO.PhysicalSupportRestriction
import TNLean.MPS.MPDO.Entropy.SALTraceTransfer
import TNLean.MPS.Operator.Simple.SimpleLocalStructure
import TNLean.MPS.Operator.PairAlphabetBridge

/-!
# Saturated area law for the BNT sectors

This file proves the sectorwise entropy argument in Appendix C.2 of
arXiv:1606.00608.  The normalized periodic state and each of its nonempty
contiguous marginals split into the mutually orthogonal BNT sectors with the
same probabilities.  The four Shannon terms in strong subadditivity cancel;
strict positivity of every sector probability then forces equality in every
sector.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Appendix C.2, lines 1760--1780.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

/-- The probability of the absorbed BNT sector in the normalized positive-
length periodic state.  The copy number is part of the weight.  Positive
normalizations are part of the definition, so there is neither an empty-chain
value nor a value obtained by dividing by a zero trace.

Source: arXiv:1606.00608, Appendix C.2, lines 1753--1770. -/
noncomputable def bntSectorProbability
    (M : MPOTensor d D) (S : MPSTensor.SectorDecomposition (Fin d × Fin d))
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q') (N : ℕ) (_hN : 0 < N)
    (_hMtrace : 0 < Matrix.trace (mpo M N))
    (_hSectorTrace : ∀ s, 0 < Matrix.trace
      (mpo (S.commonWeightAbsorbedBasis hWeight s) N))
    (s : Fin S.basisCount) : ℝ :=
  localOrthogonalSectorProbability M
    (fun j ↦ S.commonWeightAbsorbedBasis hWeight j) S.copies N s

/-- Every BNT-sector probability is strictly positive when the full and
sector chain operators have positive trace. -/
theorem bntSectorProbability_pos
    (M : MPOTensor d D) (S : MPSTensor.SectorDecomposition (Fin d × Fin d))
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q') {N : ℕ}
    (hN : 0 < N)
    (hMtrace : 0 < Matrix.trace (mpo M N))
    (hSectorTrace : ∀ s, 0 < Matrix.trace
      (mpo (S.commonWeightAbsorbedBasis hWeight s) N))
    (s : Fin S.basisCount) :
    0 < bntSectorProbability M S hWeight N hN hMtrace hSectorTrace s := by
  exact localOrthogonalSectorProbability_pos M
    (fun j ↦ S.commonWeightAbsorbedBasis hWeight j)
    S.copies S.copies_pos hMtrace hSectorTrace s

/-- The normalized full chain is the probability-weighted sum of the
normalized absorbed BNT sectors.

Source: arXiv:1606.00608, Appendix C.2, lines 1760--1770. -/
theorem normalizedMPO_eq_sum_bntSectorProbability_smul
    (M : MPOTensor d D) (S : MPSTensor.SectorDecomposition (Fin d × Fin d))
    (hM : MPTensor.SameMPV₂Pos M S.toTensor)
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q') {N : ℕ} (hN : 0 < N)
    (hMtrace : 0 < Matrix.trace (mpo M N))
    (hSectorTrace : ∀ s, 0 < Matrix.trace
      (mpo (S.commonWeightAbsorbedBasis hWeight s) N)) :
    normalizedMPO M N = ∑ s : Fin S.basisCount,
      (bntSectorProbability M S hWeight N hN hMtrace hSectorTrace s : ℂ) •
        normalizedMPO (S.commonWeightAbsorbedBasis hWeight s) N := by
  exact normalizedMPO_eq_sum_localOrthogonalSectorProbability_smul M
    (fun j ↦ S.commonWeightAbsorbedBasis hWeight j) S.copies
    (mpo_eq_sum_copies_smul_commonWeightAbsorbedBasis
      M S hM hWeight hN) hMtrace hSectorTrace

/-- Every nonempty contiguous marginal has the same BNT-sector
probabilities as the normalized full chain.

Source: arXiv:1606.00608, Appendix C.2, equation `entropiesj`,
lines 1760--1770. -/
theorem reducedBlockState_eq_sum_bntSectorProbability_smul
    (M : MPOTensor d D) (S : MPSTensor.SectorDecomposition (Fin d × Fin d))
    (hM : MPTensor.SameMPV₂Pos M S.toTensor)
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q') {N L : ℕ} (hN : 0 < N)
    (_hLpos : 0 < L) (hL : L ≤ N)
    (hMtrace : 0 < Matrix.trace (mpo M N))
    (hSectorTrace : ∀ s, 0 < Matrix.trace
      (mpo (S.commonWeightAbsorbedBasis hWeight s) N)) :
    reducedBlockState M N L hL = ∑ s : Fin S.basisCount,
      (bntSectorProbability M S hWeight N hN hMtrace hSectorTrace s : ℂ) •
        reducedBlockState (S.commonWeightAbsorbedBasis hWeight s) N L hL := by
  exact reducedBlockState_eq_sum_localOrthogonalSectorProbability_smul M
    (fun j ↦ S.commonWeightAbsorbedBasis hWeight j) S.copies hL
    (mpo_eq_sum_copies_smul_commonWeightAbsorbedBasis
      M S hM hWeight hN) hMtrace hSectorTrace

/-- Entropy of every nonempty marginal splits into the Shannon entropy of
the BNT-sector probabilities and the probability-weighted sector entropies.
The probability is fixed by the full length-`N` chain and is therefore the
same for every marginal length.

Source: arXiv:1606.00608, Appendix C.2, equation `entropiesj`,
lines 1760--1770. -/
theorem blockEntropy_eq_sum_bntSectorProbability
    (M : MPOTensor d D) (S : MPSTensor.SectorDecomposition (Fin d × Fin d))
    (hM : MPTensor.SameMPV₂Pos M S.toTensor)
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q')
    {R : (s : Fin S.basisCount) →
      Matrix (Fin (S.basisDim s)) (Fin (S.basisDim s)) ℂ}
    {ρ₃ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex S.basisDim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse
      (fun j ↦ S.basis j) C)
    (hρ₃ : IsThreeSiteFamilyClosure (fun j ↦ S.basis j) R ρ₃)
    (hη : EtaStructure ρ₃) (hR : ∀ s : Fin S.basisCount, R s ≠ 0)
    (hMpdo : IsMPDO M)
    (hSectorMpdo : ∀ s, IsMPDO
      (S.commonWeightAbsorbedBasis hWeight s))
    {N L : ℕ} (hN : 0 < N) (hLpos : 0 < L) (hL : L ≤ N)
    (hMtrace : 0 < Matrix.trace (mpo M N))
    (hSectorTrace : ∀ s, 0 < Matrix.trace
      (mpo (S.commonWeightAbsorbedBasis hWeight s) N)) :
    blockEntropy M N L hL (hMpdo N hN) =
      ∑ s : Fin S.basisCount,
        (Real.negMulLog (bntSectorProbability M S hWeight N hN
            hMtrace hSectorTrace s) +
          bntSectorProbability M S hWeight N hN hMtrace hSectorTrace s *
            blockEntropy (S.commonWeightAbsorbedBasis hWeight s)
              N L hL (hSectorMpdo s N hN)) := by
  obtain ⟨L', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hLpos)
  exact blockEntropy_eq_sum_localOrthogonalSectorProbability M
    (fun j ↦ S.commonWeightAbsorbedBasis hWeight j) S.copies
    (fun j ↦ bntSectorProjection hC hρ₃ hη hR j) S.copies_pos
    (bntSectorProjection_isOrthogonal hC hρ₃ hη hR)
    (fun hst ↦ bntSectorProjection_mul_eq_zero hC hρ₃ hη hR hst)
    hMpdo hSectorMpdo hN hL
    (mpo_eq_sum_copies_smul_commonWeightAbsorbedBasis
      M S hM hWeight hN) hMtrace hSectorTrace
    (fun s ↦ firstSiteMatrix_mul_reducedBlockState_of_ketLeftMul_eq
      (S.commonWeightAbsorbedBasis hWeight s)
      (bntSectorProjection hC hρ₃ hη hR s)
      (ketLeftMul_bntSectorProjection_commonWeightAbsorbedBasis
        S hWeight hC hρ₃ hη hR s) hL)

/-- Equality in strong subadditivity descends from the full tensor to every
absorbed BNT sector.  The four regions have lengths
\(m-1,1,N-m-1,1\).

Source: arXiv:1606.00608, Appendix C.2, lines 1760--1780. -/
theorem blockEntropy_add_blockEntropy_eq_bntSector
    (M : MPOTensor d D) (S : MPSTensor.SectorDecomposition (Fin d × Fin d))
    (hM : MPTensor.SameMPV₂Pos M S.toTensor)
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q')
    {R : (s : Fin S.basisCount) →
      Matrix (Fin (S.basisDim s)) (Fin (S.basisDim s)) ℂ}
    {ρ₃ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex S.basisDim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse
      (fun j ↦ S.basis j) C)
    (hρ₃ : IsThreeSiteFamilyClosure (fun j ↦ S.basis j) R ρ₃)
    (hη : EtaStructure ρ₃) (hR : ∀ s : Fin S.basisCount, R s ≠ 0)
    (hSAL : IsSAL M)
    (hSectorMpdo : ∀ s, IsMPDO
      (S.commonWeightAbsorbedBasis hWeight s))
    (hSectorTrace : ∀ (N : ℕ), 0 < N → ∀ s, 0 < Matrix.trace
      (mpo (S.commonWeightAbsorbedBasis hWeight s) N))
    {N m : ℕ} (hm1 : 1 ≤ m) (hmN : m ≤ N / 2)
    (s : Fin S.basisCount) :
    let K := S.commonWeightAbsorbedBasis hWeight s
    blockEntropy K N (N - 1) (Nat.sub_le N 1) (hSectorMpdo s N (by omega)) +
        blockEntropy K N 1 (by omega) (hSectorMpdo s N (by omega)) =
      blockEntropy K N m (by omega) (hSectorMpdo s N (by omega)) +
        blockEntropy K N (N - m) (Nat.sub_le N m) (hSectorMpdo s N (by omega)) := by
  classical
  dsimp only
  let hMpdo : IsMPDO M := Classical.choose hSAL
  have hN : 0 < N := by omega
  have hMtrace : 0 < Matrix.trace (mpo M N) := by
    apply Matrix.PosSemidef.trace_pos_of_ne_zero (hMpdo N hN)
    intro hzero
    exact (Classical.choose_spec hSAL).1 N hN (by
      rw [hzero, Matrix.trace_zero])
  have hGlobal := mutualInfoChain_eq_of_isSAL M hSAL
    (N := N) (L := 1) (L' := m) (by omega) (by omega) hm1 hmN
  simp only [mutualInfoChain_eq] at hGlobal
  have hEABC := blockEntropy_eq_sum_bntSectorProbability (L := N - 1)
    M S hM hWeight hC hρ₃ hη hR hMpdo hSectorMpdo hN (by omega)
      (Nat.sub_le N 1) hMtrace (hSectorTrace N hN)
  have hEB := blockEntropy_eq_sum_bntSectorProbability (L := 1)
    M S hM hWeight hC hρ₃ hη hR hMpdo hSectorMpdo hN (by omega)
      (by omega) hMtrace (hSectorTrace N hN)
  have hEAB := blockEntropy_eq_sum_bntSectorProbability (L := m)
    M S hM hWeight hC hρ₃ hη hR hMpdo hSectorMpdo hN (by omega)
      (by omega) hMtrace (hSectorTrace N hN)
  have hEBC := blockEntropy_eq_sum_bntSectorProbability (L := N - m)
    M S hM hWeight hC hρ₃ hη hR hMpdo hSectorMpdo hN (by omega)
      (Nat.sub_le N m) hMtrace (hSectorTrace N hN)
  rw [hEABC, hEB, hEAB, hEBC] at hGlobal
  let p : Fin S.basisCount → ℝ := fun t ↦
    bntSectorProbability M S hWeight N hN hMtrace (hSectorTrace N hN) t
  let L : Fin S.basisCount → ℝ := fun t ↦
    blockEntropy (S.commonWeightAbsorbedBasis hWeight t)
        N (N - 1) (Nat.sub_le N 1) (hSectorMpdo t N hN) +
      blockEntropy (S.commonWeightAbsorbedBasis hWeight t)
        N 1 (by omega) (hSectorMpdo t N hN)
  let U : Fin S.basisCount → ℝ := fun t ↦
    blockEntropy (S.commonWeightAbsorbedBasis hWeight t)
        N m (by omega) (hSectorMpdo t N hN) +
      blockEntropy (S.commonWeightAbsorbedBasis hWeight t)
        N (N - m) (Nat.sub_le N m) (hSectorMpdo t N hN)
  have hsum : ∑ t, p t * L t = ∑ t, p t * U t := by
    simp only [p, L, U]
    simp_rw [mul_add, Finset.sum_add_distrib]
    simp_rw [Finset.sum_add_distrib] at hGlobal
    linarith [hGlobal]
  have hle : ∀ t, L t ≤ U t := by
    intro t
    let K := S.commonWeightAbsorbedBasis hWeight t
    have hineq := ssa_block_entropy K
      (N := N) (a := m - 1) (b := 1) (c := N - m - 1)
      (by omega) (hSectorMpdo t N hN) (ne_of_gt (hSectorTrace N hN t))
    rw [blockEntropy_congr K N
      (show (m - 1) + 1 + (N - m - 1) = N - 1 by omega)
      (by omega) (Nat.sub_le N 1) (hSectorMpdo t N hN)] at hineq
    rw [blockEntropy_congr K N (show (m - 1) + 1 = m by omega)
      (by omega) (by omega) (hSectorMpdo t N hN)] at hineq
    rw [blockEntropy_congr K N (show 1 + (N - m - 1) = N - m by omega)
      (by omega) (Nat.sub_le N m) (hSectorMpdo t N hN)] at hineq
    exact hineq
  exact eq_of_weighted_sum_eq_of_pos_of_le p L U
    (fun t ↦ bntSectorProbability_pos M S hWeight hN hMtrace
      (hSectorTrace N hN) t) hle hsum s

/-- Every absorbed BNT representative satisfies the saturated area law once
the source projector selection, sector positivity, and strict sector
normalizations are available.

Source: arXiv:1606.00608, Appendix C.2, lines 1753--1781. -/
theorem commonWeightAbsorbedBasis_isSAL_of_projectorSelection
    (M : MPOTensor d D) (S : MPSTensor.SectorDecomposition (Fin d × Fin d))
    (hM : MPTensor.SameMPV₂Pos M S.toTensor)
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q')
    {R : (s : Fin S.basisCount) →
      Matrix (Fin (S.basisDim s)) (Fin (S.basisDim s)) ℂ}
    {ρ₃ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex S.basisDim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse
      (fun j ↦ S.basis j) C)
    (hρ₃ : IsThreeSiteFamilyClosure (fun j ↦ S.basis j) R ρ₃)
    (hη : EtaStructure ρ₃) (hR : ∀ s : Fin S.basisCount, R s ≠ 0)
    (hSAL : IsSAL M)
    (hSectorMpdo : ∀ s, IsMPDO
      (S.commonWeightAbsorbedBasis hWeight s))
    (hSectorTrace : ∀ (N : ℕ), 0 < N → ∀ s, 0 < Matrix.trace
      (mpo (S.commonWeightAbsorbedBasis hWeight s) N))
    (s : Fin S.basisCount) :
    IsSAL (S.commonWeightAbsorbedBasis hWeight s) := by
  let K := S.commonWeightAbsorbedBasis hWeight s
  refine ⟨hSectorMpdo s, fun N hN ↦ ne_of_gt (hSectorTrace N hN s), ?_⟩
  intro N L hL hLN
  have hEqL := blockEntropy_add_blockEntropy_eq_bntSector
    M S hM hWeight hC hρ₃ hη hR hSAL hSectorMpdo hSectorTrace
      (N := N) (m := L) hL (Nat.le_of_lt hLN) s
  have hEqSucc := blockEntropy_add_blockEntropy_eq_bntSector
    M S hM hWeight hC hρ₃ hη hR hSAL hSectorMpdo hSectorTrace
      (N := N) (m := L + 1) (by omega) (by omega) s
  simp only [mutualInfoChain_eq]
  dsimp only at hEqL hEqSucc
  linarith [hEqL, hEqSucc]

/-- Every absorbed BNT representative of a simple tensor satisfies the
saturated area law.

The conclusion follows by decomposing each of the four marginals in strong
subadditivity into the same orthogonal sectors.  Their Shannon contributions
cancel, and strict positivity of every sector probability forces equality in
each sector separately.

**Source hypothesis (biCF):** the one-letter simultaneous span is precisely
the block-injective canonical-form assumption imposed at the start of Case II
in arXiv:1606.00608, line 1628.  It supplies the common left inverse used in
the source proof.  The relation with finite physical blocking is recorded in
`docs/paper-gaps/cpgsv17_bicf_block_separation.tex`.

Source: arXiv:1606.00608, Appendix C.2, lines 1748--1781. -/
theorem commonWeightAbsorbedBasis_isSAL_of_sameMPV₂Pos
    {D : ℕ} (M : MPOTensor d D)
    (S : MPSTensor.SectorDecomposition (Fin d × Fin d)) (hTotal : S.totalDim = D)
    (X : (s : Fin S.totalCopies) → GL (Fin (S.flatDim s)) ℂ)
    (hEq : ∀ i : Fin d × Fin d,
      M i =
        cast (by rw [hTotal] :
            Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ =
              Matrix (Fin D) (Fin D) ℂ)
          ((MPSTensor.globalGaugeOfBlocks X :
                Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) *
            S.toTensor i *
            (((MPSTensor.globalGaugeOfBlocks X)⁻¹ :
                GL (Fin S.totalDim) ℂ) :
              Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ)))
    (hM : MPTensor.SameMPV₂Pos M S.toTensor)
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q')
    (hnonNil : ∀ j,
      ¬ IsNilpotent (physTraceTransfer (S.basis j)))
    (hSpan : MPSTensor.WordTupleSpanTop S.basis 1)
    (hSAL : IsSAL M) (hZCL : IsSourceZCL M)
    (s : Fin S.basisCount) :
    IsSAL (S.commonWeightAbsorbedBasis hWeight s) := by
  obtain ⟨W, _hlocal, _hcompression⟩ :=
    exists_bntProjectorSelection_positiveLength_of_sameMPV₂Pos_isSAL
      M S hM hWeight hnonNil hSpan hSAL
  apply commonWeightAbsorbedBasis_isSAL_of_projectorSelection
    M S hM hWeight W.hC W.hρ W.hη W.hR hSAL
  · intro t
    exact commonWeightAbsorbedBasis_isMPDO_of_sameMPV₂Pos_isSAL
      M S hM hWeight hnonNil hSpan hSAL t
  · intro N hN t
    exact trace_mpo_commonWeightAbsorbedBasis_pos
      M S hTotal X hEq hM hZCL hWeight hnonNil hSpan hSAL t hN

/-- Every common-weight-absorbed BNT representative inherits the four Case-II
properties available before the structural classification: one-site injectivity, positivity on
all positive chain lengths, saturation of the area law, and literal physical-trace idempotence.

The ambient SAL normalization makes its physical-trace transfer nonzero. Hence ambient literal
idempotence also supplies the scale-invariant relation needed by the existing sectorwise entropy
argument. The literal block equation itself is retained separately in the conclusion.

**Scope restriction (Case-II normality):** This theorem completes one-site injectivity, MPDO
positivity, SAL, and literal physical-trace idempotence for each absorbed BNT representative.
It does not assert `MPTensor.IsNormalTensor`: coefficient absorption rescales the transfer
spectral radius by the squared coefficient modulus, while the global canonical-form normalization
does not force every coefficient to have modulus one. The normal Case-I structural theorem
therefore remains unavailable sectorwise. This boundary is recorded in
<https://sirui-lu.com/QICLean/paper-gaps/cpgsv17_pf_rank_one.pdf>.

Source: arXiv:1606.00608, Appendix C.2, lines 1745--1782. -/
theorem commonWeightAbsorbedBasis_caseII_properties_of_literal_ZCL
    {D : ℕ} (M : MPOTensor d D)
    (S : MPSTensor.SectorDecomposition (Fin d × Fin d)) (hTotal : S.totalDim = D)
    (X : (s : Fin S.totalCopies) → GL (Fin (S.flatDim s)) ℂ)
    (hEq : ∀ i : Fin d × Fin d,
      M i =
        cast (by rw [hTotal] :
            Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ =
              Matrix (Fin D) (Fin D) ℂ)
          ((MPSTensor.globalGaugeOfBlocks X :
                Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) *
            S.toTensor i *
            (((MPSTensor.globalGaugeOfBlocks X)⁻¹ :
                GL (Fin S.totalDim) ℂ) :
              Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ)))
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q')
    (hnonNil : ∀ j,
      ¬ IsNilpotent (physTraceTransfer (S.basis j)))
    (hSpan : MPSTensor.WordTupleSpanTop S.basis 1)
    (hSAL : IsSAL M)
    (hZCL_sq : physTraceTransfer M * physTraceTransfer M = physTraceTransfer M)
    (s : Fin S.basisCount) :
    Kraus.IsInjective (S.commonWeightAbsorbedBasis hWeight s) ∧
      IsMPDO (S.commonWeightAbsorbedBasis hWeight s) ∧
      IsSAL (S.commonWeightAbsorbedBasis hWeight s) ∧
      physTraceTransfer (S.commonWeightAbsorbedBasis hWeight s) *
          physTraceTransfer (S.commonWeightAbsorbedBasis hWeight s) =
        physTraceTransfer (S.commonWeightAbsorbedBasis hWeight s) := by
  subst D
  have hGauge : MPTensor.GaugeEquiv S.toTensor M := by
    refine ⟨MPSTensor.globalGaugeOfBlocks X, ?_⟩
    intro i
    simpa using hEq i
  have hM : MPTensor.SameMPV₂Pos M S.toTensor :=
    fun N _hN σ ↦ (hGauge.sameMPV N σ).symm
  have hSourceZCL : IsSourceZCL M :=
    hSAL.isSourceZCL_of_physTraceTransfer_sq hZCL_sq
  exact ⟨commonWeightAbsorbedBasis_isInjective S hWeight hSpan s,
    commonWeightAbsorbedBasis_isMPDO_of_sameMPV₂Pos_isSAL
      M S hM hWeight hnonNil hSpan hSAL s,
    commonWeightAbsorbedBasis_isSAL_of_sameMPV₂Pos
      M S rfl X hEq hM hWeight hnonNil hSpan hSAL hSourceZCL s,
    commonWeightAbsorbedBasis_physTraceTransfer_sq_of_literal_ZCL
      M S rfl X hEq hZCL_sq hWeight s⟩

end MPOTensor

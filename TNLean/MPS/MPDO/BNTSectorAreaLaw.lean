/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinSum
import TNLean.MPS.MPDO.BNTSectorAnalyticProperties
import TNLean.MPS.MPDO.LocalOrthogonalSumAreaLaw
import TNLean.MPS.MPDO.PhysicalSupportRestriction
import TNLean.MPS.MPDO.SimpleLocalStructure

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
    (M : MPOTensor d D) (S : MPSTensor.SectorDecomposition (d * d))
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q') (N : ℕ) (_hN : 0 < N)
    (_hMtrace : 0 < Matrix.trace (mpo M N))
    (_hSectorTrace : ∀ s, 0 < Matrix.trace
      (mpo (commonWeightAbsorbedBasisMPOTensor S hWeight s) N))
    (s : Fin S.basisCount) : ℝ :=
  localOrthogonalSectorProbability M
    (fun j ↦ commonWeightAbsorbedBasisMPOTensor S hWeight j) S.copies N s

/-- Every BNT-sector probability is strictly positive when the full and
sector chain operators have positive trace. -/
theorem bntSectorProbability_pos
    (M : MPOTensor d D) (S : MPSTensor.SectorDecomposition (d * d))
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q') {N : ℕ}
    (hN : 0 < N)
    (hMtrace : 0 < Matrix.trace (mpo M N))
    (hSectorTrace : ∀ s, 0 < Matrix.trace
      (mpo (commonWeightAbsorbedBasisMPOTensor S hWeight s) N))
    (s : Fin S.basisCount) :
    0 < bntSectorProbability M S hWeight N hN hMtrace hSectorTrace s := by
  exact localOrthogonalSectorProbability_pos M
    (fun j ↦ commonWeightAbsorbedBasisMPOTensor S hWeight j)
    S.copies S.copies_pos hMtrace hSectorTrace s

/-- The normalized full chain is the probability-weighted sum of the
normalized absorbed BNT sectors.

Source: arXiv:1606.00608, Appendix C.2, lines 1760--1770. -/
theorem normalizedMPO_eq_sum_bntSectorProbability_smul
    (M : MPOTensor d D) (S : MPSTensor.SectorDecomposition (d * d))
    (hM : MPSTensor.SameMPV₂Pos M.toMPSTensor S.toTensor)
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q') {N : ℕ} (hN : 0 < N)
    (hMtrace : 0 < Matrix.trace (mpo M N))
    (hSectorTrace : ∀ s, 0 < Matrix.trace
      (mpo (commonWeightAbsorbedBasisMPOTensor S hWeight s) N)) :
    normalizedMPO M N = ∑ s : Fin S.basisCount,
      (bntSectorProbability M S hWeight N hN hMtrace hSectorTrace s : ℂ) •
        normalizedMPO (commonWeightAbsorbedBasisMPOTensor S hWeight s) N := by
  exact normalizedMPO_eq_sum_localOrthogonalSectorProbability_smul M
    (fun j ↦ commonWeightAbsorbedBasisMPOTensor S hWeight j) S.copies
    (mpo_eq_sum_copies_smul_commonWeightAbsorbedBasisMPOTensor
      M S hM hWeight hN) hMtrace hSectorTrace

/-- Left local invariance fixes the first site of every normalized periodic
state.

Source: arXiv:1606.00608, Appendix C.2, lines 1733--1770. -/
private theorem firstSiteMatrix_mul_normalizedMPO_of_ketLeftMul_eq
    (M : MPOTensor d D) (P : Matrix (Fin d) (Fin d) ℂ)
    (hPM : M.ketLeftMul P = M) (N : ℕ) :
    firstSiteMatrix P N * normalizedMPO M (N + 1) = normalizedMPO M (N + 1) := by
  ext σ τ
  obtain ⟨a, σ', rfl⟩ : ∃ a σ', σ = Fin.cons a σ' :=
    ⟨σ 0, σ ∘ Fin.succ, (Fin.cons_self_tail σ).symm⟩
  obtain ⟨b, τ', rfl⟩ : ∃ b τ', τ = Fin.cons b τ' :=
    ⟨τ 0, τ ∘ Fin.succ, (Fin.cons_self_tail τ).symm⟩
  rw [firstSiteMatrix_mul_apply]
  simp only [Fin.cons_zero, Function.comp_def, Fin.cons_succ, normalizedMPO,
    Matrix.smul_apply, smul_eq_mul, mpo_cons_cons]
  have hPMab := congrFun (congrFun hPM a) b
  simp only [ketLeftMul] at hPMab
  calc
    ∑ i : Fin d, P a i *
        ((mpo M (N + 1)).trace⁻¹ *
          Matrix.trace (M i b * evalWord M (List.ofFn σ') (List.ofFn τ')))
        = (mpo M (N + 1)).trace⁻¹ *
            ∑ i : Fin d, P a i *
              Matrix.trace (M i b * evalWord M (List.ofFn σ') (List.ofFn τ')) := by
          simpa only [mul_comm, mul_left_comm, mul_assoc] using
            Fintype.sum_mul_mul_eq_mul_sum_mul
              (mpo M (N + 1)).trace⁻¹ (fun i => P a i)
              (fun i => Matrix.trace (M i b * evalWord M (List.ofFn σ') (List.ofFn τ')))
    _ = (mpo M (N + 1)).trace⁻¹ *
        Matrix.trace ((∑ i : Fin d, P a i • M i b) *
          evalWord M (List.ofFn σ') (List.ofFn τ')) := by
      rw [sum_mul_trace_eq_trace_sum_smul]
    _ = (mpo M (N + 1)).trace⁻¹ *
        Matrix.trace (M a b * evalWord M (List.ofFn σ') (List.ofFn τ')) := by
      rw [hPMab]

/-- Left local invariance is preserved by taking a nonempty contiguous
marginal. -/
private theorem firstSiteMatrix_mul_reducedBlockState_of_ketLeftMul_eq
    (M : MPOTensor d D) (P : Matrix (Fin d) (Fin d) ℂ)
    (hPM : M.ketLeftMul P = M) {N L : ℕ} (hL : L + 1 ≤ N) :
    firstSiteMatrix P L * reducedBlockState M N (L + 1) hL =
      reducedBlockState M N (L + 1) hL := by
  obtain ⟨N', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  exact firstSiteMatrix_mul_reducedBlockState_of_mul_normalizedMPO M P hL
    (firstSiteMatrix_mul_normalizedMPO_of_ketLeftMul_eq M P hPM N')

/-- Every nonempty contiguous marginal has the same BNT-sector
probabilities as the normalized full chain.

Source: arXiv:1606.00608, Appendix C.2, equation `entropiesj`,
lines 1760--1770. -/
theorem reducedBlockState_eq_sum_bntSectorProbability_smul
    (M : MPOTensor d D) (S : MPSTensor.SectorDecomposition (d * d))
    (hM : MPSTensor.SameMPV₂Pos M.toMPSTensor S.toTensor)
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q') {N L : ℕ} (hN : 0 < N)
    (_hLpos : 0 < L) (hL : L ≤ N)
    (hMtrace : 0 < Matrix.trace (mpo M N))
    (hSectorTrace : ∀ s, 0 < Matrix.trace
      (mpo (commonWeightAbsorbedBasisMPOTensor S hWeight s) N)) :
    reducedBlockState M N L hL = ∑ s : Fin S.basisCount,
      (bntSectorProbability M S hWeight N hN hMtrace hSectorTrace s : ℂ) •
        reducedBlockState (commonWeightAbsorbedBasisMPOTensor S hWeight s) N L hL := by
  exact reducedBlockState_eq_sum_localOrthogonalSectorProbability_smul M
    (fun j ↦ commonWeightAbsorbedBasisMPOTensor S hWeight j) S.copies hL
    (mpo_eq_sum_copies_smul_commonWeightAbsorbedBasisMPOTensor
      M S hM hWeight hN) hMtrace hSectorTrace

/-- Entropy of every nonempty marginal splits into the Shannon entropy of
the BNT-sector probabilities and the probability-weighted sector entropies.
The probability is fixed by the full length-`N` chain and is therefore the
same for every marginal length.

Source: arXiv:1606.00608, Appendix C.2, equation `entropiesj`,
lines 1760--1770. -/
theorem blockEntropy_eq_sum_bntSectorProbability
    (M : MPOTensor d D) (S : MPSTensor.SectorDecomposition (d * d))
    (hM : MPSTensor.SameMPV₂Pos M.toMPSTensor S.toTensor)
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q')
    {R : (s : Fin S.basisCount) →
      Matrix (Fin (S.basisDim s)) (Fin (S.basisDim s)) ℂ}
    {ρ₃ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex S.basisDim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse
      (fun j ↦ S.basisMPOTensor j) C)
    (hρ₃ : IsThreeSiteFamilyClosure (fun j ↦ S.basisMPOTensor j) R ρ₃)
    (hη : EtaStructure ρ₃) (hR : ∀ s : Fin S.basisCount, R s ≠ 0)
    (hMpdo : IsMPDO M)
    (hSectorMpdo : ∀ s, IsMPDO
      (commonWeightAbsorbedBasisMPOTensor S hWeight s))
    {N L : ℕ} (hN : 0 < N) (hLpos : 0 < L) (hL : L ≤ N)
    (hMtrace : 0 < Matrix.trace (mpo M N))
    (hSectorTrace : ∀ s, 0 < Matrix.trace
      (mpo (commonWeightAbsorbedBasisMPOTensor S hWeight s) N)) :
    blockEntropy M N L hL (hMpdo N hN) =
      ∑ s : Fin S.basisCount,
        (Real.negMulLog (bntSectorProbability M S hWeight N hN
            hMtrace hSectorTrace s) +
          bntSectorProbability M S hWeight N hN hMtrace hSectorTrace s *
            blockEntropy (commonWeightAbsorbedBasisMPOTensor S hWeight s)
              N L hL (hSectorMpdo s N hN)) := by
  obtain ⟨L', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hLpos)
  exact blockEntropy_eq_sum_localOrthogonalSectorProbability M
    (fun j ↦ commonWeightAbsorbedBasisMPOTensor S hWeight j) S.copies
    (fun j ↦ bntSectorProjection hC hρ₃ hη hR j) S.copies_pos
    (bntSectorProjection_isOrthogonal hC hρ₃ hη hR)
    (fun hst ↦ bntSectorProjection_mul_eq_zero hC hρ₃ hη hR hst)
    hMpdo hSectorMpdo hN hL
    (mpo_eq_sum_copies_smul_commonWeightAbsorbedBasisMPOTensor
      M S hM hWeight hN) hMtrace hSectorTrace
    (fun s ↦ firstSiteMatrix_mul_reducedBlockState_of_ketLeftMul_eq
      (commonWeightAbsorbedBasisMPOTensor S hWeight s)
      (bntSectorProjection hC hρ₃ hη hR s)
      (ketLeftMul_bntSectorProjection_commonWeightAbsorbedBasis
        S hWeight hC hρ₃ hη hR s) hL)

/-- Equality in strong subadditivity descends from the full tensor to every
absorbed BNT sector.  The four regions have lengths
\(m-1,1,N-m-1,1\).

Source: arXiv:1606.00608, Appendix C.2, lines 1760--1780. -/
theorem blockEntropy_add_blockEntropy_eq_bntSector
    (M : MPOTensor d D) (S : MPSTensor.SectorDecomposition (d * d))
    (hM : MPSTensor.SameMPV₂Pos M.toMPSTensor S.toTensor)
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q')
    {R : (s : Fin S.basisCount) →
      Matrix (Fin (S.basisDim s)) (Fin (S.basisDim s)) ℂ}
    {ρ₃ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex S.basisDim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse
      (fun j ↦ S.basisMPOTensor j) C)
    (hρ₃ : IsThreeSiteFamilyClosure (fun j ↦ S.basisMPOTensor j) R ρ₃)
    (hη : EtaStructure ρ₃) (hR : ∀ s : Fin S.basisCount, R s ≠ 0)
    (hSAL : IsSAL M)
    (hSectorMpdo : ∀ s, IsMPDO
      (commonWeightAbsorbedBasisMPOTensor S hWeight s))
    (hSectorTrace : ∀ (N : ℕ), 0 < N → ∀ s, 0 < Matrix.trace
      (mpo (commonWeightAbsorbedBasisMPOTensor S hWeight s) N))
    {N m : ℕ} (hm1 : 1 ≤ m) (hmN : m ≤ N / 2)
    (s : Fin S.basisCount) :
    let K := commonWeightAbsorbedBasisMPOTensor S hWeight s
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
  simp only [mutualInfoChain] at hGlobal
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
    blockEntropy (commonWeightAbsorbedBasisMPOTensor S hWeight t)
        N (N - 1) (Nat.sub_le N 1) (hSectorMpdo t N hN) +
      blockEntropy (commonWeightAbsorbedBasisMPOTensor S hWeight t)
        N 1 (by omega) (hSectorMpdo t N hN)
  let U : Fin S.basisCount → ℝ := fun t ↦
    blockEntropy (commonWeightAbsorbedBasisMPOTensor S hWeight t)
        N m (by omega) (hSectorMpdo t N hN) +
      blockEntropy (commonWeightAbsorbedBasisMPOTensor S hWeight t)
        N (N - m) (Nat.sub_le N m) (hSectorMpdo t N hN)
  have hsum : ∑ t, p t * L t = ∑ t, p t * U t := by
    simp only [p, L, U]
    simp_rw [mul_add, Finset.sum_add_distrib]
    simp_rw [Finset.sum_add_distrib] at hGlobal
    linarith [hGlobal]
  have hle : ∀ t, L t ≤ U t := by
    intro t
    let K := commonWeightAbsorbedBasisMPOTensor S hWeight t
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
theorem commonWeightAbsorbedBasisMPOTensor_isSAL_of_projectorSelection
    (M : MPOTensor d D) (S : MPSTensor.SectorDecomposition (d * d))
    (hM : MPSTensor.SameMPV₂Pos M.toMPSTensor S.toTensor)
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q')
    {R : (s : Fin S.basisCount) →
      Matrix (Fin (S.basisDim s)) (Fin (S.basisDim s)) ℂ}
    {ρ₃ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex S.basisDim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse
      (fun j ↦ S.basisMPOTensor j) C)
    (hρ₃ : IsThreeSiteFamilyClosure (fun j ↦ S.basisMPOTensor j) R ρ₃)
    (hη : EtaStructure ρ₃) (hR : ∀ s : Fin S.basisCount, R s ≠ 0)
    (hSAL : IsSAL M)
    (hSectorMpdo : ∀ s, IsMPDO
      (commonWeightAbsorbedBasisMPOTensor S hWeight s))
    (hSectorTrace : ∀ (N : ℕ), 0 < N → ∀ s, 0 < Matrix.trace
      (mpo (commonWeightAbsorbedBasisMPOTensor S hWeight s) N))
    (s : Fin S.basisCount) :
    IsSAL (commonWeightAbsorbedBasisMPOTensor S hWeight s) := by
  let K := commonWeightAbsorbedBasisMPOTensor S hWeight s
  refine ⟨hSectorMpdo s, fun N hN ↦ ne_of_gt (hSectorTrace N hN s), ?_⟩
  intro N L hL hLN
  have hEqL := blockEntropy_add_blockEntropy_eq_bntSector
    M S hM hWeight hC hρ₃ hη hR hSAL hSectorMpdo hSectorTrace
      (N := N) (m := L) hL (Nat.le_of_lt hLN) s
  have hEqSucc := blockEntropy_add_blockEntropy_eq_bntSector
    M S hM hWeight hC hρ₃ hη hR hSAL hSectorMpdo hSectorTrace
      (N := N) (m := L + 1) (by omega) (by omega) s
  simp only [mutualInfoChain]
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
theorem commonWeightAbsorbedBasisMPOTensor_isSAL_of_sameMPV₂Pos
    {D : ℕ} (M : MPOTensor d D)
    (S : MPSTensor.SectorDecomposition (d * d)) (hTotal : S.totalDim = D)
    (X : (s : Fin S.totalCopies) → GL (Fin (S.flatDim s)) ℂ)
    (hEq : ∀ i : Fin (d * d),
      M.toMPSTensor i =
        cast (by rw [hTotal] :
            Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ =
              Matrix (Fin D) (Fin D) ℂ)
          ((MPSTensor.globalGaugeOfBlocks X :
                Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) *
            S.toTensor i *
            (((MPSTensor.globalGaugeOfBlocks X)⁻¹ :
                GL (Fin S.totalDim) ℂ) :
              Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ)))
    (hM : MPSTensor.SameMPV₂Pos M.toMPSTensor S.toTensor)
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q')
    (hnonNil : ∀ j,
      ¬ IsNilpotent (doubledPhysTraceTransfer d (S.basis j)))
    (hSpan : MPSTensor.WordTupleSpanTop S.basis 1)
    (hSAL : IsSAL M) (hZCL : IsSourceZCL M)
    (s : Fin S.basisCount) :
    IsSAL (commonWeightAbsorbedBasisMPOTensor S hWeight s) := by
  obtain ⟨C, hC, hη, _hlocal, _hcompression⟩ :=
    exists_bntProjectorSelection_positiveLength_of_sameMPV₂Pos_isSAL
      M S hM hWeight hnonNil hSpan hSAL
  let hClosure :=
    reducedBlockState_four_threeSiteFamilyClosure_nonzero_closing
      M S hM hWeight hnonNil hSAL
  apply commonWeightAbsorbedBasisMPOTensor_isSAL_of_projectorSelection
    M S hM hWeight hC hClosure.1 hη hClosure.2 hSAL
  · intro t
    exact commonWeightAbsorbedBasisMPOTensor_isMPDO_of_sameMPV₂Pos_isSAL
      M S hM hWeight hnonNil hSpan hSAL t
  · intro N hN t
    exact trace_mpo_commonWeightAbsorbedBasisMPOTensor_pos
      M S hTotal X hEq hM hZCL hWeight hnonNil hSpan hSAL t hN

/-- Every common-weight-absorbed BNT representative inherits the four Case-II
properties available before the structural classification: one-site injectivity, positivity on
all positive chain lengths, saturation of the area law, and literal physical-trace idempotence.

The ambient SAL normalization makes its physical-trace transfer nonzero. Hence ambient literal
idempotence also supplies the scale-invariant relation needed by the existing sectorwise entropy
argument. The literal block equation itself is retained separately in the conclusion.

**Scope restriction (Case-II normality):** This theorem completes one-site injectivity, MPDO
positivity, SAL, and literal physical-trace idempotence for each absorbed BNT representative.
It does not assert `MPSTensor.IsNormalTensor`: coefficient absorption rescales the transfer
spectral radius by the squared coefficient modulus, while the global canonical-form normalization
does not force every coefficient to have modulus one. The normal Case-I structural theorem
therefore remains unavailable sectorwise. This boundary is recorded in
`docs/paper-gaps/cpgsv17_pf_rank_one.tex`.

Source: arXiv:1606.00608, Appendix C.2, lines 1745--1782. -/
theorem commonWeightAbsorbedBasisMPOTensor_caseII_properties_of_literal_ZCL
    {D : ℕ} (M : MPOTensor d D)
    (S : MPSTensor.SectorDecomposition (d * d)) (hTotal : S.totalDim = D)
    (X : (s : Fin S.totalCopies) → GL (Fin (S.flatDim s)) ℂ)
    (hEq : ∀ i : Fin (d * d),
      M.toMPSTensor i =
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
      ¬ IsNilpotent (doubledPhysTraceTransfer d (S.basis j)))
    (hSpan : MPSTensor.WordTupleSpanTop S.basis 1)
    (hSAL : IsSAL M)
    (hZCL_sq : physTraceTransfer M * physTraceTransfer M = physTraceTransfer M)
    (s : Fin S.basisCount) :
    (commonWeightAbsorbedBasisMPOTensor S hWeight s).IsInjective ∧
      IsMPDO (commonWeightAbsorbedBasisMPOTensor S hWeight s) ∧
      IsSAL (commonWeightAbsorbedBasisMPOTensor S hWeight s) ∧
      physTraceTransfer (commonWeightAbsorbedBasisMPOTensor S hWeight s) *
          physTraceTransfer (commonWeightAbsorbedBasisMPOTensor S hWeight s) =
        physTraceTransfer (commonWeightAbsorbedBasisMPOTensor S hWeight s) := by
  subst D
  have hGauge : MPSTensor.GaugeEquiv S.toTensor M.toMPSTensor := by
    refine ⟨MPSTensor.globalGaugeOfBlocks X, ?_⟩
    intro i
    simpa using hEq i
  have hM : MPSTensor.SameMPV₂Pos M.toMPSTensor S.toTensor :=
    fun N _hN σ ↦ (hGauge.sameMPV N σ).symm
  have hTransfer : physTraceTransfer M ≠ 0 := by
    intro hZero
    exact (Classical.choose_spec hSAL).1 1 Nat.zero_lt_one (by
      rw [trace_mpo_eq_trace_verticalLoop_pow, verticalLoop_eq_physTraceTransfer, hZero]
      simp)
  have hSourceZCL : IsSourceZCL M :=
    isSourceZCL_of_physTraceTransfer_sq M hTransfer hZCL_sq
  exact ⟨commonWeightAbsorbedBasisMPOTensor_isInjective S hWeight hSpan s,
    commonWeightAbsorbedBasisMPOTensor_isMPDO_of_sameMPV₂Pos_isSAL
      M S hM hWeight hnonNil hSpan hSAL s,
    commonWeightAbsorbedBasisMPOTensor_isSAL_of_sameMPV₂Pos
      M S rfl X hEq hM hWeight hnonNil hSpan hSAL hSourceZCL s,
    commonWeightAbsorbedBasisMPOTensor_physTraceTransfer_sq_of_literal_ZCL
      M S rfl X hEq hZCL_sq hWeight s⟩

end MPOTensor

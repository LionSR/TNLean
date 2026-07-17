/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.EntropyDecomposition
import TNLean.MPS.MPDO.BNTSectorAnalyticProperties
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

private theorem mul_eq_self_of_isHermitian_of_mul_eq_self
    {n : Type*} [Fintype n]
    {A P : Matrix n n ℂ} (hA : A.IsHermitian) (hP : P.IsHermitian)
    (hleft : P * A = A) :
    A * P = A := by
  classical
  have hstar := congrArg Matrix.conjTranspose hleft
  simpa only [Matrix.conjTranspose_mul, hA.eq, hP.eq] using hstar

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
  (S.copies s : ℝ) *
    (Matrix.trace (mpo (commonWeightAbsorbedBasisMPOTensor S hWeight s) N)).re /
      (Matrix.trace (mpo M N)).re

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
  rw [bntSectorProbability]
  have hMre : 0 < (Matrix.trace (mpo M N)).re :=
    (RCLike.pos_iff.mp hMtrace).1
  have hSre : 0 < (Matrix.trace
      (mpo (commonWeightAbsorbedBasisMPOTensor S hWeight s) N)).re :=
    (RCLike.pos_iff.mp (hSectorTrace s)).1
  exact div_pos (mul_pos (by exact_mod_cast S.copies_pos s) hSre) hMre

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
  classical
  have hMtraceEq : Matrix.trace (mpo M N) =
      ((Matrix.trace (mpo M N)).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using (RCLike.pos_iff.mp hMtrace).2
  have hSectorTraceEq : ∀ s, Matrix.trace
      (mpo (commonWeightAbsorbedBasisMPOTensor S hWeight s) N) =
        ((Matrix.trace
          (mpo (commonWeightAbsorbedBasisMPOTensor S hWeight s) N)).re : ℂ) :=
    fun s ↦ by
      apply Complex.ext
      · rfl
      · simpa using (RCLike.pos_iff.mp (hSectorTrace s)).2
  have hpComplex (s : Fin S.basisCount) :
      (bntSectorProbability M S hWeight N hN hMtrace hSectorTrace s : ℂ) =
        (S.copies s : ℂ) *
          Matrix.trace (mpo (commonWeightAbsorbedBasisMPOTensor S hWeight s) N) /
            Matrix.trace (mpo M N) := by
    rw [bntSectorProbability, hMtraceEq, hSectorTraceEq s]
    norm_num
  have hdecomp :=
    mpo_eq_sum_copies_smul_commonWeightAbsorbedBasisMPOTensor M S hM hWeight hN
  rw [normalizedMPO]
  nth_rewrite 2 [hdecomp]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [normalizedMPO, hpComplex]
  simp only [smul_smul]
  congr 1
  field_simp [(ne_of_gt hMtrace), (ne_of_gt (hSectorTrace s))]

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
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
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
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  ext u v
  obtain ⟨a, u', rfl⟩ : ∃ a u', u = Fin.cons a u' :=
    ⟨u 0, u ∘ Fin.succ, (Fin.cons_self_tail u).symm⟩
  obtain ⟨b, v', rfl⟩ : ∃ b v', v = Fin.cons b v' :=
    ⟨v 0, v ∘ Fin.succ, (Fin.cons_self_tail v).symm⟩
  rw [firstSiteMatrix_mul_apply]
  simp only [Fin.cons_zero, Function.comp_def, Fin.cons_succ]
  simp_rw [reducedBlockState_eq_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  simp only [normalizedMPO, Matrix.smul_apply, smul_eq_mul, mpo_apply,
    mpoMatrixEntry]
  let z : Fin N → Fin d :=
    Fin.append u' w ∘ Fin.cast (show N = L + (N + 1 - (L + 1)) by omega)
  let z' : Fin N → Fin d :=
    Fin.append v' w ∘ Fin.cast (show N = L + (N + 1 - (L + 1)) by omega)
  have htail (r : Fin L → Fin d) (x : Fin d) :
      (fun i : Fin N ↦ Fin.append (Fin.cons x r) w
        (Fin.cast (show N + 1 = L + 1 + (N + 1 - (L + 1)) by omega) i.succ)) =
      Fin.append r w ∘
        Fin.cast (show N = L + (N + 1 - (L + 1)) by omega) := by
    funext i
    by_cases hi : i.val < L
    · have hleft : Fin.cast
          (show N + 1 = L + 1 + (N + 1 - (L + 1)) by omega) i.succ =
          Fin.castAdd (N + 1 - (L + 1)) (Fin.succ ⟨i.val, hi⟩) := by
        apply Fin.ext
        simp
      have hright : Fin.cast
          (show N = L + (N + 1 - (L + 1)) by omega) i =
          Fin.castAdd (N + 1 - (L + 1)) ⟨i.val, hi⟩ := by
        apply Fin.ext
        simp
      rw [hleft]
      change Fin.append (Fin.cons x r) w
        (Fin.castAdd (N + 1 - (L + 1)) (Fin.succ ⟨i.val, hi⟩)) =
          Fin.append r w (Fin.cast
            (show N = L + (N + 1 - (L + 1)) by omega) i)
      rw [hright, Fin.append_left, Fin.append_left, Fin.cons_succ]
    · let k : Fin (N + 1 - (L + 1)) := ⟨i.val - L, by omega⟩
      have hleft : Fin.cast
          (show N + 1 = L + 1 + (N + 1 - (L + 1)) by omega) i.succ =
          Fin.natAdd (L + 1) k := by
        apply Fin.ext
        simp [k]
        omega
      have hright : Fin.cast
          (show N = L + (N + 1 - (L + 1)) by omega) i =
          Fin.natAdd L k := by
        apply Fin.ext
        simp [k]
        omega
      rw [hleft]
      change Fin.append (Fin.cons x r) w (Fin.natAdd (L + 1) k) =
        Fin.append r w (Fin.cast
          (show N = L + (N + 1 - (L + 1)) by omega) i)
      rw [hright, Fin.append_right, Fin.append_right]
  have hword (x : Fin d) :
      List.ofFn (Fin.append (Fin.cons x u') w ∘
        Fin.cast (show N + 1 = L + 1 + (N + 1 - (L + 1)) by omega)) =
        x :: List.ofFn z := by
    rw [List.ofFn_succ]
    congr 1
    exact congrArg List.ofFn (htail u' x)
  have hword' :
      List.ofFn (Fin.append (Fin.cons b v') w ∘
        Fin.cast (show N + 1 = L + 1 + (N + 1 - (L + 1)) by omega)) =
        b :: List.ofFn z' := by
    rw [List.ofFn_succ]
    congr 1
    exact congrArg List.ofFn (htail v' b)
  simp_rw [hword, hword', evalWord_cons]
  have hPMab := congrFun (congrFun hPM a) b
  simp only [ketLeftMul] at hPMab
  calc
    ∑ x : Fin d, P a x *
        ((mpo M (N + 1)).trace⁻¹ *
          Matrix.trace (M x b * evalWord M (List.ofFn z) (List.ofFn z')))
        = (mpo M (N + 1)).trace⁻¹ *
            ∑ x : Fin d, P a x *
              Matrix.trace (M x b * evalWord M (List.ofFn z) (List.ofFn z')) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring
    _ = (mpo M (N + 1)).trace⁻¹ *
        Matrix.trace ((∑ x : Fin d, P a x • M x b) *
          evalWord M (List.ofFn z) (List.ofFn z')) := by
      rw [sum_mul_trace_eq_trace_sum_smul]
    _ = (mpo M (N + 1)).trace⁻¹ *
        Matrix.trace (M a b * evalWord M (List.ofFn z) (List.ofFn z')) := by
      rw [hPMab]

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
  classical
  have hfull := normalizedMPO_eq_sum_bntSectorProbability_smul
    M S hM hWeight hN hMtrace hSectorTrace
  ext u v
  rw [reducedBlockState_eq_sum]
  simp_rw [hfull, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp_rw [reducedBlockState_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]

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
  classical
  obtain ⟨L, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hLpos)
  let K : (s : Fin S.basisCount) → MPOTensor d (S.basisDim s) :=
    fun s ↦ commonWeightAbsorbedBasisMPOTensor S hWeight s
  let p : Fin S.basisCount → ℝ := fun s ↦
    bntSectorProbability M S hWeight N hN hMtrace hSectorTrace s
  let ρ : (s : Fin S.basisCount) →
      Matrix (Fin (L + 1) → Fin d) (Fin (L + 1) → Fin d) ℂ :=
    fun s ↦ reducedBlockState (K s) N (L + 1) hL
  let Q : Fin S.basisCount →
      Matrix (Fin (L + 1) → Fin d) (Fin (L + 1) → Fin d) ℂ :=
    fun s ↦ firstSiteMatrix (bntSectorProjection hC hρ₃ hη hR s) L
  have hp : ∀ s, 0 < p s := fun s ↦
    bntSectorProbability_pos M S hWeight hN hMtrace hSectorTrace s
  have hρpos : ∀ s, (ρ s).PosSemidef := fun s ↦
    reducedBlockState_posSemidef (K s) N (L + 1) hL (hSectorMpdo s N hN)
  have hρtrace : ∀ s, Matrix.trace (ρ s) = 1 := fun s ↦
    reducedBlockState_trace (K s) N (L + 1) hL (ne_of_gt (hSectorTrace s))
  have hQherm : ∀ s, (Q s).IsHermitian := fun s ↦
    firstSiteMatrix_isHermitian
      (bntSectorProjection_isOrthogonal hC hρ₃ hη hR s).1 L
  have hQρ : ∀ s, Q s * ρ s = ρ s := fun s ↦
    firstSiteMatrix_mul_reducedBlockState_of_ketLeftMul_eq
      (K s) (bntSectorProjection hC hρ₃ hη hR s)
        (ketLeftMul_bntSectorProjection_commonWeightAbsorbedBasis
          S hWeight hC hρ₃ hη hR s) hL
  have hρQ : ∀ s, ρ s * Q s = ρ s := fun s ↦
    mul_eq_self_of_isHermitian_of_mul_eq_self (hρpos s).isHermitian
      (hQherm s) (hQρ s)
  have hQorth : ∀ s t, s ≠ t → Q s * Q t = 0 := by
    intro s t hst
    change firstSiteMatrix (bntSectorProjection hC hρ₃ hη hR s) L *
      firstSiteMatrix (bntSectorProjection hC hρ₃ hη hR t) L = 0
    rw [firstSiteMatrix_mul_firstSiteMatrix,
      bntSectorProjection_mul_eq_zero hC hρ₃ hη hR hst]
    ext u v
    simp [firstSiteMatrix]
  have hsum : reducedBlockState M N (L + 1) hL =
      ∑ s, (p s : ℂ) • ρ s := by
    exact reducedBlockState_eq_sum_bntSectorProbability_smul
      M S hM hWeight hN (by omega) hL hMtrace hSectorTrace
  have hadd := vonNeumannEntropy_eq_sum_of_pairwise_annihilating_supports
    (reducedBlockState M N (L + 1) hL)
    (reducedBlockState_isHermitian M N (L + 1) hL (hMpdo N hN))
    (fun s ↦ (p s : ℂ) • ρ s) Q
    (fun s ↦ ((hρpos s).smul (a := (p s : ℂ))
      (by exact_mod_cast (hp s).le)).isHermitian)
    hsum (fun s ↦ ⟨by rw [Matrix.mul_smul, hQρ],
      by rw [Matrix.smul_mul, hρQ]⟩) hQorth
  calc
    blockEntropy M N (L + 1) hL (hMpdo N hN) =
        ∑ s, vonNeumannEntropy ((p s : ℂ) • ρ s)
          (((hρpos s).smul (a := (p s : ℂ))
            (by exact_mod_cast (hp s).le)).isHermitian) := hadd
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      simpa only [K, p, ρ, blockEntropy, add_comm] using
        vonNeumannEntropy_smul (hρpos s) (hρtrace s) (p s)

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

/-- Every absorbed normal representative of a simple tensor satisfies the
saturated area law.

The conclusion follows by decomposing each of the four marginals in strong
subadditivity into the same orthogonal sectors.  Their Shannon contributions
cancel, and strict positivity of every sector probability forces equality in
each sector separately.

**Scope restriction (common blocking):** the one-letter simultaneous span is
the blocked form used to construct the common left inverse.  Its derivation
from the unrestricted biCF statement is recorded in
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

end MPOTensor

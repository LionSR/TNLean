/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.EntropyScaling.QutritFamily
import QICLean.Analysis.EntropySubadditivity
import QICLean.Entropy.FilterOptimizer
import QICLean.Entropy.RegionEntropy
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Tactic.Ring

/-!
# Regional entropy of the qutrit family

The state in arXiv:0705.0292v2, equation `eq:magicstate`, has entropy at most
`Real.binEntropy p + p * N * Real.log 2` on every region. Entropies here use
natural logarithms; the bound in bits is obtained by dividing by `Real.log 2`.
-/

open Matrix
open scoped BigOperators InnerProductSpace ComplexOrder

namespace TNLean.MPS.AreaLaw.EntropyScaling

private noncomputable def regionalMatrix {N : ℕ} (A : Finset (Fin (N + N)))
    (ψ : EuclideanSpace ℂ (Fin (N + N) → Fin 3)) :=
  schmidtCoeffMatrix (WithLp.ofLp (Entropy.cutVector A ψ))

private theorem regionalMatrix_sum {N : ℕ} (A : Finset (Fin (N + N)))
    {ι : Type*} [Fintype ι] (ψ : ι → EuclideanSpace ℂ (Fin (N + N) → Fin 3)) :
    regionalMatrix A (∑ i, ψ i) = ∑ i, regionalMatrix A (ψ i) := by
  ext a b
  simp [regionalMatrix, schmidtCoeffMatrix, Matrix.sum_apply]

private theorem regionalMatrix_smul {N : ℕ} (A : Finset (Fin (N + N)))
    (c : ℂ) (ψ : EuclideanSpace ℂ (Fin (N + N) → Fin 3)) :
    regionalMatrix A (c • ψ) = c • regionalMatrix A ψ := rfl

private theorem regionalMatrix_basis {N : ℕ} (A : Finset (Fin (N + N)))
    (w : Fin (N + N) → Fin 3) :
    regionalMatrix A (EuclideanSpace.basisFun _ ℂ w) =
      Matrix.vecMulVec
        (EuclideanSpace.basisFun _ ℂ ((Entropy.cutEquiv (fun _ ↦ 3) A w).1))
        (EuclideanSpace.basisFun _ ℂ ((Entropy.cutEquiv (fun _ ↦ 3) A w).2)) := by
  ext a b
  simp [regionalMatrix, schmidtCoeffMatrix, EuclideanSpace.basisFun_apply,
    Matrix.vecMulVec, Equiv.symm_apply_eq, Prod.ext_iff, ite_and]
  split_ifs <;> rfl

private theorem qutritState_split (N : ℕ) (p : ℝ) :
    qutritState N p =
      (Real.sqrt (1 - p) : ℂ) • EuclideanSpace.basisFun _ ℂ
        (Fin.append (qutritWord N (.inl ())) (qutritWord N (.inl ()))) +
      (Real.sqrt (p / (2 : ℝ) ^ N) : ℂ) •
        ∑ x : Fin N → Fin 2, EuclideanSpace.basisFun _ ℂ
          (Fin.append (qutritWord N (.inr x)) (qutritWord N (.inr x))) := by
  simp only [qutritState, Fintype.sum_sum_type, qutritWeight, Fintype.sum_unique,
    Finset.smul_sum]

private theorem qutritState_decomposition (N : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    qutritState N p = (Real.sqrt (1 - p) : ℂ) • qutritState N 0 +
      (Real.sqrt p : ℂ) • qutritState N 1 := by
  simp only [qutritState_split, sub_zero, sub_self, Real.sqrt_one, Real.sqrt_zero,
    zero_div, Complex.ofReal_zero, Complex.ofReal_one, zero_smul, one_smul,
    add_zero, zero_add, smul_smul]
  rw [Real.sqrt_div hp, Real.sqrt_div zero_le_one]
  simp only [Real.sqrt_one, Complex.ofReal_div, Complex.ofReal_one, mul_one_div]

private theorem regionalMatrix_decomposition {N : ℕ} (A : Finset (Fin (N + N)))
    {p : ℝ} (hp : 0 ≤ p) :
    regionalMatrix A (qutritState N p) =
      (Real.sqrt (1 - p) : ℂ) • regionalMatrix A (qutritState N 0) +
      (Real.sqrt p : ℂ) • regionalMatrix A (qutritState N 1) := by
  rw [qutritState_decomposition N hp]
  rfl

private theorem binaryWord_lt_two {N : ℕ} (x : Fin N → Fin 2) (v : Fin (N + N)) :
    (Fin.append (qutritWord N (.inr x)) (qutritWord N (.inr x)) v).val < 2 := by
  refine Fin.addCases ?_ ?_ v
  · exact fun i ↦ (Fin.append_left (qutritWord N (.inr x))
      (qutritWord N (.inr x)) i).symm ▸ (x i).isLt
  · exact fun i ↦ (Fin.append_right (qutritWord N (.inr x))
      (qutritWord N (.inr x)) i).symm ▸ (x i).isLt

private theorem qutritState_one_apply_eq_zero {N : ℕ}
    (σ : Fin (N + N) → Fin 3) (v : Fin (N + N)) (hσ : σ v = 2) :
    qutritState N 1 σ = 0 := by
  have hne (x : Fin N → Fin 2) :
      σ ≠ Fin.append (qutritWord N (.inr x)) (qutritWord N (.inr x)) := by
    intro h
    have hlt := binaryWord_lt_two x v
    rw [← h, hσ] at hlt
    exact (by decide : ¬ ((2 : Fin 3).val < 2)) hlt
  simp [qutritState_split, EuclideanSpace.basisFun_apply, hne]

private theorem qutritState_zero (N : ℕ) :
    qutritState N 0 = EuclideanSpace.basisFun _ ℂ (fun _ ↦ (2 : Fin 3)) := by
  have hflag : Fin.append (fun _ : Fin N ↦ (2 : Fin 3)) (fun _ : Fin N ↦ 2) =
      (fun _ ↦ 2) := funext (Fin.addCases (fun i ↦ Fin.append_left _ _ i)
        (fun i ↦ Fin.append_right _ _ i))
  simp [qutritState_split, qutritWord, hflag]

private theorem regionalMatrix_zero {N : ℕ} (A : Finset (Fin (N + N))) :
    regionalMatrix A (qutritState N 0) =
      Matrix.vecMulVec (EuclideanSpace.basisFun _ ℂ (fun _ ↦ (2 : Fin 3)))
        (EuclideanSpace.basisFun _ ℂ (fun _ ↦ (2 : Fin 3))) := by
  rw [qutritState_zero, regionalMatrix_basis]
  rfl

private theorem regionalMatrix_one_flagColumn {N : ℕ}
    {A : Finset (Fin (N + N))} (hA : A ≠ Finset.univ)
    (a : Entropy.RegionConfig (fun _ : Fin (N + N) ↦ 3) A) :
    regionalMatrix A (qutritState N 1) a (fun _ ↦ 2) = 0 := by
  obtain ⟨v, hv⟩ := (show ∃ v, v ∉ A by
    simpa only [ne_eq, Finset.eq_univ_iff_forall, not_forall] using hA)
  exact qutritState_one_apply_eq_zero _ v
    (Entropy.cutEquiv_symm_apply_not_mem (n := fun _ : Fin (N + N) ↦ 3) a (fun _ ↦ 2) hv)

private theorem regionalMatrix_cross_eq_zero {N : ℕ}
    {A : Finset (Fin (N + N))} (hA : A ≠ Finset.univ) :
    regionalMatrix A (qutritState N 0) * (regionalMatrix A (qutritState N 1))ᴴ = 0 := by
  rw [regionalMatrix_zero]
  ext a b
  simp [Matrix.mul_apply, Matrix.vecMulVec, EuclideanSpace.basisFun_apply,
    regionalMatrix_one_flagColumn hA]

/-- Tracing out a nonempty complement removes the flag–binary cross terms in
arXiv:0705.0292v2, `eq:magicstate`, lines 382–386. The endpoints are included. -/
theorem regionState_qutritState_decomposition {N : ℕ}
    {A : Finset (Fin (N + N))} (hA : A ≠ Finset.univ)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    Entropy.regionState A (qutritState N p) =
      ((1 - p : ℝ) : ℂ) • Entropy.regionState A (qutritState N 0) +
      (p : ℂ) • Entropy.regionState A (qutritState N 1) := by
  have hcross := regionalMatrix_cross_eq_zero hA
  have hcross' := congrArg Matrix.conjTranspose hcross
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_zero] at hcross'
  simp only [Entropy.regionState, partialTraceRight_vecMulVec_eq]
  change regionalMatrix A (qutritState N p) * (regionalMatrix A (qutritState N p))ᴴ =
    ((1 - p : ℝ) : ℂ) •
        (regionalMatrix A (qutritState N 0) * (regionalMatrix A (qutritState N 0))ᴴ) +
      (p : ℂ) •
        (regionalMatrix A (qutritState N 1) * (regionalMatrix A (qutritState N 1))ᴴ)
  rw [regionalMatrix_decomposition A hp, Matrix.conjTranspose_add]
  simp only [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
    Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    hcross, hcross', smul_zero, add_zero, zero_add]
  simp only [← pow_two, Complex.ofReal_sqrt_sq _ (sub_nonneg.mpr hp'),
    Complex.ofReal_sqrt_sq _ hp]

private theorem rank_regionalMatrix_one_le {N : ℕ} (A : Finset (Fin (N + N))) :
    (regionalMatrix A (qutritState N 1)).rank ≤ 2 ^ N := by
  let L : Matrix (Entropy.RegionConfig (fun _ : Fin (N + N) ↦ 3) A)
      (Fin N → Fin 2) ℂ := fun a x ↦
    (Real.sqrt (1 / (2 : ℝ) ^ N) : ℂ) * EuclideanSpace.basisFun _ ℂ
      ((Entropy.cutEquiv (fun _ ↦ 3) A
        (Fin.append (qutritWord N (.inr x)) (qutritWord N (.inr x)))).1) a
  let R : Matrix (Fin N → Fin 2) ({v : Fin (N + N) // v ∉ A} → Fin 3) ℂ := fun x b ↦
    EuclideanSpace.basisFun _ ℂ
      ((Entropy.cutEquiv (fun _ ↦ 3) A
        (Fin.append (qutritWord N (.inr x)) (qutritWord N (.inr x)))).2) b
  have hfact : regionalMatrix A (qutritState N 1) = L * R := by
    rw [qutritState_split]
    simp only [sub_self, Real.sqrt_zero, Complex.ofReal_zero, zero_smul, zero_add,
      regionalMatrix_smul, regionalMatrix_sum, regionalMatrix_basis]
    ext a b
    rw [Matrix.mul_apply]
    simp only [Matrix.smul_apply, Matrix.sum_apply,
      Matrix.vecMulVec_apply, L, R, smul_eq_mul, Finset.mul_sum, mul_assoc]
  rw [hfact]
  exact (Matrix.rank_mul_le_left L R).trans (by simpa using Matrix.rank_le_card_width L)

private theorem rank_regionState_one_le {N : ℕ} (A : Finset (Fin (N + N))) :
    (Entropy.regionState A (qutritState N 1)).rank ≤ 2 ^ N := by
  rw [Entropy.regionState, partialTraceRight_vecMulVec_eq]
  exact (Matrix.rank_mul_le_left _ _).trans (rank_regionalMatrix_one_le A)

private theorem rank_regionState_zero_le {N : ℕ} (A : Finset (Fin (N + N))) :
    (Entropy.regionState A (qutritState N 0)).rank ≤ 1 := by
  rw [Entropy.regionState, partialTraceRight_vecMulVec_eq]
  change (regionalMatrix A (qutritState N 0) * (regionalMatrix A (qutritState N 0))ᴴ).rank ≤ 1
  refine (Matrix.rank_mul_le_left _ _).trans ?_
  rw [regionalMatrix_zero]
  exact Matrix.rank_vecMulVec_le _ _

private theorem trace_regionState_qutritState {N : ℕ} (hN : 0 < N)
    (A : Finset (Fin (N + N))) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    (Entropy.regionState A (qutritState N p)).trace = 1 := by
  simp [Entropy.trace_regionState, norm_qutritState hN hp hp']

private theorem regionEntropy_qutritState_zero {N : ℕ} (hN : 0 < N)
    (A : Finset (Fin (N + N))) : Entropy.regionEntropy A (qutritState N 0) = 0 :=
  vonNeumannEntropy_eq_zero_of_rank_le_one (Entropy.regionState_posSemidef _ _)
    (trace_regionState_qutritState hN A le_rfl zero_le_one) (rank_regionState_zero_le A)

private theorem regionEntropy_qutritState_one_le {N : ℕ} (hN : 0 < N)
    (A : Finset (Fin (N + N))) :
    Entropy.regionEntropy A (qutritState N 1) ≤ (N : ℝ) * Real.log 2 := by
  have hρ := Entropy.regionState_posSemidef A (qutritState N 1)
  have htr := trace_regionState_qutritState hN A zero_le_one le_rfl
  refine (vonNeumannEntropy_le_log_rank hρ htr).trans ?_
  have hlog := Real.log_le_log
    (show (0 : ℝ) < (Entropy.regionState A (qutritState N 1)).rank by
      exact_mod_cast hρ.rank_pos_of_trace_one htr)
    (show ((Entropy.regionState A (qutritState N 1)).rank : ℝ) ≤ (2 : ℝ) ^ N by
      exact_mod_cast rank_regionState_one_le A)
  simpa only [Real.log_pow] using hlog

/-- The entire qutrit chain is pure; its entropy is zero.
Source: arXiv:0705.0292v2, `eq:magicstate`, lines 382–386. -/
theorem regionEntropy_qutritState_univ {N : ℕ} (hN : 0 < N)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    Entropy.regionEntropy Finset.univ (qutritState N p) = 0 := by
  apply vonNeumannEntropy_eq_zero_of_rank_le_one
    (Entropy.regionState_posSemidef _ _) (trace_regionState_qutritState hN _ hp hp')
  rw [Entropy.regionState, partialTraceRight_vecMulVec_eq]
  refine (Matrix.rank_mul_le_left _ _).trans ?_
  change (regionalMatrix Finset.univ (qutritState N p)).rank ≤ 1
  simpa using Matrix.rank_le_card_width (regionalMatrix Finset.univ (qutritState N p))

/-- Every region of the state in `eq:magicstate` has entropy at most
`H₂(p) + p N log 2`, including the empty and full regions. Entropy uses natural
logarithms. Source: arXiv:0705.0292v2, lines 382–388 and 426–430. -/
theorem regionEntropy_qutritState_le {N : ℕ} (hN : 0 < N)
    (A : Finset (Fin (N + N))) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    Entropy.regionEntropy A (qutritState N p) ≤
      Real.binEntropy p + p * (N : ℝ) * Real.log 2 := by
  by_cases hA : A = Finset.univ
  · subst A
    rw [regionEntropy_qutritState_univ hN hp hp']
    exact add_nonneg (Real.binEntropy_nonneg hp hp') (by positivity)
  have h0 := Entropy.regionState_posSemidef A (qutritState N 0)
  have h1 := Entropy.regionState_posSemidef A (qutritState N 1)
  have htr0 := trace_regionState_qutritState hN A le_rfl zero_le_one
  have htr1 := trace_regionState_qutritState hN A zero_le_one le_rfl
  have hadd := vonNeumannEntropy_add_le
    (h0.smul (show (0 : ℂ) ≤ ((1 - p : ℝ) : ℂ) by exact_mod_cast sub_nonneg.mpr hp'))
    (h1.smul (show (0 : ℂ) ≤ (p : ℂ) by exact_mod_cast hp))
  rw [vonNeumannEntropy_smul h0 htr0, vonNeumannEntropy_smul h1 htr1] at hadd
  have hmix : Entropy.regionEntropy A (qutritState N p) ≤
      (1 - p) * Entropy.regionEntropy A (qutritState N 0) + Real.negMulLog (1 - p) +
        (p * Entropy.regionEntropy A (qutritState N 1) + Real.negMulLog p) := by
    simpa only [Entropy.regionEntropy, regionState_qutritState_decomposition hA hp hp']
      using hadd
  rw [regionEntropy_qutritState_zero hN A, mul_zero, zero_add] at hmix
  have hbound := mul_le_mul_of_nonneg_left (regionEntropy_qutritState_one_le hN A) hp
  refine (hmix.trans (add_le_add le_rfl (add_le_add hbound le_rfl))).trans_eq ?_
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  ring

/-- The empty region has zero entropy. Source: arXiv:0705.0292v2,
`eq:magicstate`, lines 382–386. -/
theorem regionEntropy_qutritState_empty {N : ℕ} (hN : 0 < N)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    Entropy.regionEntropy ∅ (qutritState N p) = 0 := by
  apply vonNeumannEntropy_eq_zero_of_rank_le_one
    (Entropy.regionState_posSemidef _ _) (trace_regionState_qutritState hN _ hp hp')
  simpa using Matrix.rank_le_card_width (Entropy.regionState ∅ (qutritState N p))

/-- Every region of the source's choice `p_N = 1/N` has entropy at most two bits.
The displayed inequality uses natural logarithms. Source: arXiv:0705.0292v2,
lines 387–388 and 426–430. -/
theorem regionEntropy_qutritFamily_le {N : ℕ} (hN : 0 < N)
    (A : Finset (Fin (N + N))) :
    Entropy.regionEntropy A (qutritFamily N) ≤ 2 * Real.log 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNge : (1 : ℝ) ≤ N := by exact_mod_cast hN
  calc
    Entropy.regionEntropy A (qutritFamily N) ≤
        Real.binEntropy ((N : ℝ)⁻¹) + (N : ℝ)⁻¹ * N * Real.log 2 :=
      regionEntropy_qutritState_le hN A (inv_nonneg.mpr hNpos.le)
        (inv_le_one_of_one_le₀ hNge)
    _ = Real.binEntropy ((N : ℝ)⁻¹) + Real.log 2 := by
      rw [inv_mul_cancel₀ hNpos.ne', one_mul]
    _ ≤ Real.log 2 + Real.log 2 := add_le_add Real.binEntropy_le_log_two le_rfl
    _ = 2 * Real.log 2 := by ring

end TNLean.MPS.AreaLaw.EntropyScaling

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.SupportedMarginalChannel
import TNLean.Channel.WeightedHilbertSchmidt

/-!
# Whitened bipartite operators as Choi matrices

This file combines the supported-marginal channel, the full-support weighted
Hilbert--Schmidt contraction, and the rectangular Choi rank estimate.  The
first marginal is written in an eigenbasis, so its transpose is equal to
itself.  The input transpose nevertheless appears explicitly in the general
Choi covariance identity below.

## Main declarations

* `Matrix.rectangularChoi_singleKrausMap_comp_comp`: Choi covariance under
  input and output congruences, including the input transpose.
* `Matrix.supportedMarginalWhitenedState`: the raw congruence used for
  order-two whitening in a first-marginal eigenbasis.
* `Matrix.supportedMarginalWhitenedState_posSemidef`: the defining congruence
  preserves positive semidefiniteness.
* `Matrix.supportedMarginalWhitenedState_eq_rectangularChoi`: this congruence
  is exactly the Choi matrix of the weighted supported-marginal map.
* `Matrix.supportedMarginalWhitenedState_frobenius_sq_le_operatorSchmidtRank`:
  the full-support whitened Choi estimate.
* `Matrix.supportedMarginalWhitenedState_trace_sq_re_le_operatorSchmidtRank`:
  the full-support estimate in trace-square form.

## References

* S. Beigi, *Sandwiched Rényi Divergence Satisfies Data Processing
  Inequality*, J. Math. Phys. 54 (2013), 122202, arXiv:1306.5920,
  Theorem 6 and equation (18).
-/

open scoped Matrix BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.Frobenius

namespace Matrix

variable {α β : Type*} [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β]

omit [DecidableEq β] in
/-- Choi matrices transform under input and output congruences with the
transpose of the input congruence matrix.

The transpose is forced by the convention
`J(L)_{(i,a),(j,b)} = L(Eᵢⱼ)_{a,b}`. -/
theorem rectangularChoi_singleKrausMap_comp_comp
    (Φ : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ)
    (A : Matrix α α ℂ) (B : Matrix β β ℂ) :
    rectangularChoi ((singleKrausMap B).comp (Φ.comp (singleKrausMap A))) =
      singleKrausMap (A.transpose ⊗ₖ B) (rectangularChoi Φ) := by
  have hinput (i j : α) :
      A * single i j 1 * Aᴴ =
        ∑ r, ∑ s, (A r i * star (A s j)) • single r s 1 := by
    rw [matrix_eq_sum_single (A * single i j 1 * Aᴴ)]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    rw [Matrix.smul_single]
    congr 1
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single,
      Matrix.of_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single i]
      · simp
      · intro x _ hxi
        simp [Ne.symm hxi]
      · simp
    · intro x _ hx
      simp [Ne.symm hx]
    · simp
  ext ⟨i, a⟩ ⟨j, b⟩
  rw [rectangularChoi_apply]
  simp only [LinearMap.comp_apply, singleKrausMap_apply, hinput,
    map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_apply,
    Matrix.transpose_apply]
  simp_rw [Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul]
  simp_rw [rectangularChoi_apply, Finset.mul_sum]
  let f : α → α → β → β → ℂ := fun r s d c ↦
    A r i * star (A s j) *
      (B a c * Φ (single r s 1) c d * star (B b d))
  change (∑ r, ∑ s, ∑ d, ∑ c, f r s d c) = _
  calc
    (∑ r, ∑ s, ∑ d, ∑ c, f r s d c) =
        ∑ s, ∑ d, ∑ r, ∑ c, f r s d c := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro c _
      dsimp only [f]
      ring

/-- The positive fourth root of a diagonal marginal, written entrywise in its
eigenbasis. -/
noncomputable def diagonalMarginalQuarter (p : α → ℝ) : Matrix α α ℂ :=
  diagonal fun i ↦ (Real.sqrt (Real.sqrt (p i)) : ℂ)

/-- The iterated functional-calculus square root of a faithful diagonal
marginal agrees with its entrywise positive fourth root. -/
theorem sqrt_sqrt_diagonal_eq_diagonalMarginalQuarter
    (p : α → ℝ) (hp : ∀ i, 0 < p i) :
    CFC.sqrt (CFC.sqrt (diagonal fun i ↦ (p i : ℂ))) =
      diagonalMarginalQuarter p := by
  have hdiag : (diagonal fun i ↦ (p i : ℂ)).PosSemidef :=
    PosSemidef.diagonal fun i ↦
      (RCLike.ofReal_nonneg (K := ℂ)).2 (le_of_lt (hp i))
  have hsqrt : CFC.sqrt (diagonal fun i ↦ (p i : ℂ)) =
      diagonal fun i ↦ (Real.sqrt (p i) : ℂ) := by
    rw [CFC.sqrt_eq_real_sqrt _ hdiag.nonneg, cfcₙ_eq_cfc,
      cfc_diagonal p Real.sqrt]
  have hsqrtDiag : (diagonal fun i ↦ (Real.sqrt (p i) : ℂ)).PosSemidef :=
    PosSemidef.diagonal fun i ↦
      (RCLike.ofReal_nonneg (K := ℂ)).2 (Real.sqrt_nonneg (p i))
  rw [hsqrt, CFC.sqrt_eq_real_sqrt _ hsqrtDiag.nonneg, cfcₙ_eq_cfc,
    cfc_diagonal (fun i ↦ Real.sqrt (p i)) Real.sqrt]
  rfl

/-- The diagonal matrix implementing the inverse-square-root input scaling of
the supported-marginal channel. -/
noncomputable def marginalInvSqrtDiagonal (p : α → ℝ) : Matrix α α ℂ :=
  diagonal (marginalInvSqrt p)

/-- The supported-marginal input scaling is congruence by the diagonal inverse
square root. -/
theorem supportedMarginalInputScaling_eq_singleKrausMap
    (p : α → ℝ) :
    supportedMarginalInputScaling p = singleKrausMap (marginalInvSqrtDiagonal p) := by
  apply LinearMap.ext
  intro X
  ext i j
  simp [supportedMarginalInputScaling, singleKrausMap_apply,
    marginalInvSqrtDiagonal, Matrix.mul_apply, marginalInvSqrt,
    Matrix.diagonal_apply]

omit [DecidableEq β] in
/-- The Choi matrix of the operator-Schmidt reshaping is the original
bipartite matrix in the natural input--output ordering. -/
theorem rectangularChoi_operatorSchmidtMap
    (ρ : Matrix (α × β) (α × β) ℂ) :
    rectangularChoi (operatorSchmidtMap ρ) = ρ := by
  ext ⟨i, a⟩ ⟨j, b⟩
  rw [rectangularChoi_apply, operatorSchmidtMap_apply]
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp [operatorBlock]
    · intro k _ hkj
      simp [Matrix.single, Ne.symm hkj]
    · simp
  · intro k _ hki
    simp [Matrix.single, Ne.symm hki]
  · simp

/-- One inverse-square-root factor cancels one diagonal fourth-root factor. -/
theorem marginalInvSqrtDiagonal_mul_diagonalMarginalQuarter
    (p : α → ℝ) (hp : ∀ i, 0 < p i) :
    marginalInvSqrtDiagonal p * diagonalMarginalQuarter p =
      (diagonalMarginalQuarter p)⁻¹ := by
  have hq (i : α) : (Real.sqrt (Real.sqrt (p i)) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.2 (Real.sqrt_pos.2 (hp i)))
  have hqdet : (diagonalMarginalQuarter p).det ≠ 0 := by
    rw [diagonalMarginalQuarter, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ hq i
  have hprod : marginalInvSqrtDiagonal p * diagonalMarginalQuarter p *
      diagonalMarginalQuarter p = 1 := by
    rw [marginalInvSqrtDiagonal, diagonalMarginalQuarter,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply, if_pos, marginalInvSqrt]
      have hsqrt : (Real.sqrt (p i) : ℂ) ≠ 0 := by
        exact_mod_cast ne_of_gt (Real.sqrt_pos.2 (hp i))
      have hsq : (Real.sqrt (Real.sqrt (p i)) : ℂ) ^ 2 =
          (Real.sqrt (p i) : ℂ) := by
        norm_cast
        exact Real.sq_sqrt (Real.sqrt_nonneg (p i))
      rw [← hsq]
      field_simp
      simp [hq i]
    · simp [hij]
  calc
    marginalInvSqrtDiagonal p * diagonalMarginalQuarter p =
        (marginalInvSqrtDiagonal p * diagonalMarginalQuarter p) *
          (diagonalMarginalQuarter p * (diagonalMarginalQuarter p)⁻¹) := by
      rw [Matrix.mul_nonsing_inv _ (Ne.isUnit hqdet), Matrix.mul_one]
    _ = (marginalInvSqrtDiagonal p * diagonalMarginalQuarter p *
          diagonalMarginalQuarter p) * (diagonalMarginalQuarter p)⁻¹ := by
      noncomm_ring
    _ = (diagonalMarginalQuarter p)⁻¹ := by rw [hprod, Matrix.one_mul]

/-- The raw same-factor congruence used for order-two whitening in an
eigenbasis of the first marginal.

If `σ = diagonal p` and `τ` is positive definite, then
`σ.transpose = σ`; hence this is
\((\sigma^T\otimes\tau)^{-1/4}\rho
(\sigma^T\otimes\tau)^{-1/4}\) in the natural `α × β` ordering.  For an
arbitrary `τ`, this definition denotes only the displayed raw congruence; no
identification with the inverse fourth power of `τ` is asserted. -/
noncomputable def supportedMarginalWhitenedState
    (ρ : Matrix (α × β) (α × β) ℂ) (p : α → ℝ) (τ : Matrix β β ℂ) :
    Matrix (α × β) (α × β) ℂ :=
  singleKrausMap
    ((diagonalMarginalQuarter p)⁻¹ ⊗ₖ
      (CFC.sqrt (CFC.sqrt τ))⁻¹) ρ

/-- The raw congruence defining `supportedMarginalWhitenedState` preserves
positive semidefiniteness.  When the two marginal weights are positive
definite, this is positivity of the order-two whitened operator. -/
theorem supportedMarginalWhitenedState_posSemidef
    (ρ : Matrix (α × β) (α × β) ℂ) (p : α → ℝ)
    (τ : Matrix β β ℂ) (hρ : ρ.PosSemidef) :
    (supportedMarginalWhitenedState ρ p τ).PosSemidef := by
  unfold supportedMarginalWhitenedState singleKrausMap
  exact hρ.mul_mul_conjTranspose_same _

/-- In a first-marginal eigenbasis, the raw congruence defining
`supportedMarginalWhitenedState` is exactly the unnormalized Choi matrix of
the weighted supported-marginal map.

The input transpose is explicit in
`rectangularChoi_singleKrausMap_comp_comp` and disappears here only because
the first marginal and its positive fourth root are diagonal.  When `τ` is
positive definite, the raw congruence is the order-two whitening used after
Beigi, arXiv:1306.5920, Theorem 6, equation (18); without this hypothesis, the
theorem is only the algebraic Choi identity displayed in its statement. -/
theorem supportedMarginalWhitenedState_eq_rectangularChoi
    (ρ : Matrix (α × β) (α × β) ℂ) (p : α → ℝ)
    (τ : Matrix β β ℂ) (hp : ∀ i, 0 < p i) :
    supportedMarginalWhitenedState ρ p τ =
      rectangularChoi
        (weightedHilbertSchmidtMap (supportedMarginalMap ρ p)
          (diagonal fun i ↦ (p i : ℂ)) τ) := by
  let σ : Matrix α α ℂ := diagonal fun i ↦ (p i : ℂ)
  let qσ := CFC.sqrt (CFC.sqrt σ)
  let qτ := CFC.sqrt (CFC.sqrt τ)
  let D := marginalInvSqrtDiagonal p
  have hqσ : qσ = diagonalMarginalQuarter p := by
    exact sqrt_sqrt_diagonal_eq_diagonalMarginalQuarter p hp
  have hscaling : supportedMarginalInputScaling p = singleKrausMap D := by
    exact supportedMarginalInputScaling_eq_singleKrausMap p
  have hDq : D * qσ = (diagonalMarginalQuarter p)⁻¹ := by
    rw [hqσ]
    exact marginalInvSqrtDiagonal_mul_diagonalMarginalQuarter p hp
  have hL : weightedHilbertSchmidtMap (supportedMarginalMap ρ p) σ τ =
      (singleKrausMap qτ⁻¹).comp
        ((operatorSchmidtMap ρ).comp (singleKrausMap (D * qσ))) := by
    apply LinearMap.ext
    intro X
    simp only [weightedHilbertSchmidtMap, supportedMarginalMap, σ, qσ, qτ,
      LinearMap.comp_apply, hscaling]
    rw [← DFunLike.congr_fun (singleKrausMap_comp D qσ) X]
    rfl
  have htranspose :
      ((diagonalMarginalQuarter p)⁻¹).transpose =
        (diagonalMarginalQuarter p)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv]
    congr 1
    simp [diagonalMarginalQuarter]
  rw [show (diagonal fun i ↦ (p i : ℂ)) = σ from rfl, hL]
  rw [rectangularChoi_singleKrausMap_comp_comp,
    rectangularChoi_operatorSchmidtMap, hDq, htranspose]
  rfl

/-- Pre- and post-composition by linear equivalences preserve the dimension of
the range of a linear map. -/
theorem finrank_range_equiv_comp_comp_equiv
    {K U U' V V' : Type*} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup U'] [Module K U']
    [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    (A : V ≃ₗ[K] V') (L : U →ₗ[K] V) (B : U' ≃ₗ[K] U) :
    Module.finrank K (LinearMap.range
      (A.toLinearMap.comp (L.comp B.toLinearMap))) =
      Module.finrank K (LinearMap.range L) := by
  change Module.finrank K (LinearMap.range
    ((A.toLinearMap.comp L).comp B.toLinearMap)) = _
  rw [LinearMap.range_comp_of_range_eq_top _ B.range]
  rw [LinearMap.range_comp]
  exact LinearEquiv.finrank_map_eq A L.range

/-- A single-Kraus congruence by an invertible matrix is the corresponding
linear equivalence. -/
theorem singleKrausMap_eq_congruenceLinearEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℂ) (hC : C.det ≠ 0) :
    singleKrausMap C = (congruenceLinearEquiv C hC).toLinearMap := by
  apply LinearMap.ext
  intro X
  exact congruenceLinearEquiv_apply C hC X |>.symm

/-- Invertible modular congruences preserve the linear rank of the weighted
Hilbert--Schmidt map. -/
theorem finrank_range_weightedHilbertSchmidtMap
    (Φ : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ)
    (σ : Matrix α α ℂ) (τ : Matrix β β ℂ)
    (hσ : σ.PosDef) (hτ : τ.PosDef) :
    Module.finrank ℂ (LinearMap.range
      (weightedHilbertSchmidtMap Φ σ τ)) =
      Module.finrank ℂ (LinearMap.range Φ) := by
  let qσ := CFC.sqrt (CFC.sqrt σ)
  let qτ := CFC.sqrt (CFC.sqrt τ)
  have hsσ_psd : (CFC.sqrt σ).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg σ)
  have hsτ_psd : (CFC.sqrt τ).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg τ)
  have hqσ_unit : IsUnit qσ :=
    (CFC.isUnit_sqrt_iff (CFC.sqrt σ) hsσ_psd.nonneg).2
      ((CFC.isUnit_sqrt_iff σ hσ.posSemidef.nonneg).2 hσ.isUnit)
  have hqτ_unit : IsUnit qτ :=
    (CFC.isUnit_sqrt_iff (CFC.sqrt τ) hsτ_psd.nonneg).2
      ((CFC.isUnit_sqrt_iff τ hτ.posSemidef.nonneg).2 hτ.isUnit)
  have hqσ_det : qσ.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det qσ).1 hqσ_unit).ne_zero
  have hqτ_det : qτ.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det qτ).1 hqτ_unit).ne_zero
  have hqτ_inv_det : qτ⁻¹.det ≠ 0 :=
    (Matrix.isUnit_nonsing_inv_det (A := qτ) (Ne.isUnit hqτ_det)).ne_zero
  rw [show weightedHilbertSchmidtMap Φ σ τ =
      (congruenceLinearEquiv qτ⁻¹ hqτ_inv_det).toLinearMap.comp
        (Φ.comp (congruenceLinearEquiv qσ hqσ_det).toLinearMap) by
    dsimp only [weightedHilbertSchmidtMap, qσ, qτ]
    rw [singleKrausMap_eq_congruenceLinearEquiv,
      singleKrausMap_eq_congruenceLinearEquiv]]
  exact finrank_range_equiv_comp_comp_equiv
    (congruenceLinearEquiv qτ⁻¹ hqτ_inv_det) Φ
    (congruenceLinearEquiv qσ hqσ_det)

/-- **Full-support, eigenbasis whitened Choi estimate.**  For a positive
bipartite operator whose first marginal is faithful and diagonal, and whose
second marginal is positive definite, the squared Frobenius norm of its
order-two whitening is at most its operator-Schmidt rank.

This combines the `p = 2` contraction from Beigi, arXiv:1306.5920,
Theorem 6, equation (18), with the rectangular Choi rank estimate.

**Scope restriction (faithful marginal supports):** Both marginals are
positive definite in the displayed coordinates.  Two-sided compression of
singular ambient marginals, including preservation of operator-Schmidt rank,
is tracked in issue #5211; construction of the output support corner is
tracked separately in issue #5225.  Both gaps are recorded in
`docs/paper-gaps/cpgsv17_mpdo_mutual_information_bound.tex`. -/
theorem supportedMarginalWhitenedState_frobenius_sq_le_operatorSchmidtRank
    (ρ : Matrix (α × β) (α × β) ℂ) (p : α → ℝ)
    (hρ : ρ.PosSemidef) (hp : ∀ i, 0 < p i)
    (hA : partialTraceRight ρ = diagonal fun i ↦ (p i : ℂ))
    (hB : (partialTraceLeft ρ).PosDef) :
    ‖supportedMarginalWhitenedState ρ p (partialTraceLeft ρ)‖ ^ 2 ≤
      operatorSchmidtRank ρ := by
  have hdiag : (diagonal fun i ↦ (p i : ℂ)).PosDef := by
    rw [posDef_diagonal_iff]
    intro i
    exact_mod_cast hp i
  have hmap := supportedMarginalMap_diagonal ρ p hp
  have hcontraction := weightedHilbertSchmidtMap_isHilbertSchmidtContraction
    (supportedMarginalMap_isKrausCPTP ρ p hρ hp hA) hdiag hB hmap
  rw [supportedMarginalWhitenedState_eq_rectangularChoi ρ p _ hp]
  calc
    ‖rectangularChoi
      (weightedHilbertSchmidtMap
        (supportedMarginalMap ρ p)
        (diagonal fun i ↦ (p i : ℂ))
        (partialTraceLeft ρ))‖ ^ 2
        ≤ Module.finrank ℂ (LinearMap.range
          (weightedHilbertSchmidtMap
            (supportedMarginalMap ρ p)
            (diagonal fun i ↦ (p i : ℂ))
            (partialTraceLeft ρ))) :=
      rectangularChoi_frobenius_sq_le_finrank_range _ hcontraction
    _ = Module.finrank ℂ (LinearMap.range (supportedMarginalMap ρ p)) := by
      exact_mod_cast finrank_range_weightedHilbertSchmidtMap
        (supportedMarginalMap ρ p) _ _ hdiag hB
    _ = operatorSchmidtRank ρ := by
      exact_mod_cast finrank_range_supportedMarginalMap ρ p hp

/-- **Full-support, eigenbasis trace-square estimate.**  Under faithful
marginal weights, the whitened operator is positive semidefinite and the real
trace of its square is at most its operator-Schmidt rank.

This is the trace-square form of the order-two estimate used after Beigi,
arXiv:1306.5920, Theorem 6, equation (18).

**Scope restriction (faithful marginal supports):** The two-sided compression
from singular ambient marginals to their supports, including preservation of
operator-Schmidt rank, remains to be proved as recorded in
`docs/paper-gaps/cpgsv17_mpdo_mutual_information_bound.tex` and issue #5211. -/
theorem supportedMarginalWhitenedState_trace_sq_re_le_operatorSchmidtRank
    (ρ : Matrix (α × β) (α × β) ℂ) (p : α → ℝ)
    (hρ : ρ.PosSemidef) (hp : ∀ i, 0 < p i)
    (hA : partialTraceRight ρ = diagonal fun i ↦ (p i : ℂ))
    (hB : (partialTraceLeft ρ).PosDef) :
    (trace (supportedMarginalWhitenedState ρ p (partialTraceLeft ρ) *
      supportedMarginalWhitenedState ρ p (partialTraceLeft ρ))).re ≤
      operatorSchmidtRank ρ := by
  have hW := supportedMarginalWhitenedState_posSemidef
    ρ p (partialTraceLeft ρ) hρ
  calc
    (trace (supportedMarginalWhitenedState ρ p (partialTraceLeft ρ) *
      supportedMarginalWhitenedState ρ p (partialTraceLeft ρ))).re =
        (trace ((supportedMarginalWhitenedState ρ p (partialTraceLeft ρ))ᴴ *
          supportedMarginalWhitenedState ρ p (partialTraceLeft ρ))).re := by
      rw [hW.isHermitian.eq]
    _ ≤ operatorSchmidtRank ρ := by
      rw [trace_conjTranspose_mul_self_re_eq_frobenius_norm_sq]
      exact supportedMarginalWhitenedState_frobenius_sq_le_operatorSchmidtRank
        ρ p hρ hp hA hB

end Matrix

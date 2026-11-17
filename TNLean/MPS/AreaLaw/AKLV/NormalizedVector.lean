/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.GlobalGap
import QICLean.Channel.ProductOverlapBootstrap

/-!
# Normalization of an approximate ground vector

A vector with a nonzero component along a unit target can be normalized and
phase corrected, with squared error at most twice the ratio of orthogonal
mass to target mass. This is the normalization used in AKLV,
arXiv:1301.1162v1, Lemma 6.3 (`l:5`, lines 1021–1052).
-/

open scoped InnerProductSpace

noncomputable section

namespace TNLean.MPS.AreaLaw.AKLV

/-- Subtracting the component along a unit vector leaves an orthogonal
vector. This is the decomposition used in AKLV, Lemmas 6.3 and 7.1. -/
theorem inner_sub_inner_smul_unit_eq_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (φ ψ : E) (hφ : ‖φ‖ = 1) : ⟪φ, ψ - ⟪φ, ψ⟫_ℂ • φ⟫_ℂ = 0 := by
  rw [inner_sub_right, inner_smul_right, inner_self_eq_one_of_norm_eq_one hφ,
    mul_one, sub_self]

/-- Normalization and a unit phase convert an orthogonal decomposition into
a squared-distance bound. Auxiliary to AKLV, Lemma 6.3. -/
theorem exists_phase_normalized_of_decomposition
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (φ χ v : E) (a : ℂ) (hφ : ‖φ‖ = 1) (ha : a ≠ 0)
    (horth : ⟪φ, v⟫_ℂ = 0) (hχ : χ = a • φ + v) :
    χ ≠ 0 ∧ ∃ θ : ℝ,
      let ψ := Complex.exp (θ * Complex.I) • ((‖χ‖ : ℂ)⁻¹ • χ)
      ‖ψ‖ = 1 ∧ ‖φ - ψ‖ ^ 2 ≤ 2 * ‖v‖ ^ 2 / ‖a‖ ^ 2 := by
  have hself : ⟪φ, φ⟫_ℂ = 1 := inner_self_eq_one_of_norm_eq_one hφ
  have hinnerχ : ⟪φ, χ⟫_ℂ = a := by
    simp only [hχ, inner_add_right, inner_smul_right, hself, mul_one, horth, add_zero]
  have hnormχ : ‖χ‖ ^ 2 = ‖a‖ ^ 2 + ‖v‖ ^ 2 := by
    rw [hχ]
    simpa only [norm_smul, hφ, mul_one, pow_two] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ)
        (a • φ) v (by simp only [inner_smul_left, horth, mul_zero])
  have hχne : χ ≠ 0 := by
    intro hz
    apply ha
    simpa only [hz, inner_zero_right] using hinnerχ.symm
  have hn : 0 < ‖χ‖ := norm_pos_iff.mpr hχne
  let u := (‖χ‖ : ℂ)⁻¹ • χ
  have hu : ‖u‖ = 1 := by
    simp only [u, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hn, inv_mul_cancel₀ hn.ne']
  have hinner : ‖⟪φ, u⟫_ℂ‖ ^ 2 = ‖a‖ ^ 2 / ‖χ‖ ^ 2 := by
    simp only [u, inner_smul_right, hinnerχ, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hn, mul_pow, inv_pow, div_eq_inv_mul]
  have hdef : 1 - ‖⟪φ, u⟫_ℂ‖ ^ 2 = ‖v‖ ^ 2 / ‖χ‖ ^ 2 := by
    rw [hinner]
    apply (eq_div_iff (pow_ne_zero _ hn.ne')).mpr
    rw [sub_mul, one_mul, div_mul_cancel₀ _ (pow_ne_zero _ hn.ne'), hnormχ]
    ring
  have hbound : 1 - ‖⟪φ, u⟫_ℂ‖ ^ 2 ≤ ‖v‖ ^ 2 / ‖a‖ ^ 2 := by
    rw [hdef]
    apply div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos (norm_pos_iff.mpr ha))
    nlinarith [sq_nonneg ‖v‖]
  obtain ⟨θ, -, hθ⟩ := exists_isMinOn_sq_norm_sub_exp_smul_le_of_gap
    (by norm_num : (0 : ℝ) < 1) hφ hu
    (by simpa only [one_mul, norm_inner_symm] using hbound)
  refine ⟨hχne, θ, ?_, ?_⟩
  · change ‖Complex.exp (θ * Complex.I) • u‖ = 1
    rw [norm_smul, Complex.norm_exp_ofReal_mul_I, hu, mul_one]
  · change ‖φ - Complex.exp (θ * Complex.I) • u‖ ^ 2 ≤ _
    convert hθ using 1
    ring

/-- Nonzero normalization and unit phase preserve Schmidt rank. This is the
rank invariance used at every normalized step of AKLV, Lemma 6.3. -/
theorem schmidtRank_phase_normalized_eq
    {m n : Type*} [Fintype m] [Fintype n]
    (χ : EuclideanSpace ℂ (m × n)) (hne : χ ≠ 0) (θ : ℝ) :
    Matrix.schmidtRank (WithLp.ofLp (Complex.exp (θ * Complex.I) •
      ((‖χ‖ : ℂ)⁻¹ • χ))) = Matrix.schmidtRank (WithLp.ofLp χ) := by
  rw [WithLp.ofLp_smul, Matrix.schmidtRank_smul_eq_of_ne_zero _
    (Complex.exp_ne_zero _) _, WithLp.ofLp_smul,
    Matrix.schmidtRank_smul_eq_of_ne_zero _
      (inv_ne_zero (by exact_mod_cast (norm_pos_iff.mpr hne).ne')) _]

end TNLean.MPS.AreaLaw.AKLV

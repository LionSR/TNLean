/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.NormalizedVector

/-!
# Filtering a low-rank seed with a nonzero target overlap

A unit seed with overlap at least μ with a fixed unit target gives a normalized
filtered approximant with squared error at most 2δ/μ² and Schmidt rank at most
D times the seed rank. This is the normalization and rank step of AKLV,
arXiv:1301.1162v1, Lemmas 6.3 and 7.1, applied to a supplied approximate
projector. Construction of that operator is separate.
-/

open scoped InnerProductSpace

noncomputable section

namespace TNLean.MPS.AreaLaw.AKLV

/-- An actual normalized filtered seed, with explicit squared error and
Schmidt-rank bounds. The seed overlap is a lower bound and the output
normalization is proved nonzero. AKLV, Lemmas 6.3 and 7.1. -/
theorem exists_filtered_approximation_of_overlap
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (K : Matrix (m × n) (m × n) ℂ) (φ ξ : EuclideanSpace ℂ (m × n))
    (hφ : ‖φ‖ = 1) (hξ : ‖ξ‖ = 1) (hfix : Matrix.toEuclideanLin K φ = φ)
    (μ δ : ℝ) (hμ : 0 < μ) (hδ : 0 ≤ δ) (hoverlap : μ ≤ ‖⟪φ, ξ⟫_ℂ‖)
    (hperp : ∀ v : EuclideanSpace ℂ (m × n), ‖v‖ = 1 → ⟪φ, v⟫_ℂ = 0 →
      ⟪φ, Matrix.toEuclideanLin K v⟫_ℂ = 0 ∧ ‖Matrix.toEuclideanLin K v‖ ^ 2 ≤ δ)
    (D R : ℕ) (hD : Matrix.operatorSchmidtRank K ≤ D)
    (hR : Matrix.schmidtRank (WithLp.ofLp ξ) ≤ R) :
    Matrix.toEuclideanLin K ξ ≠ 0 ∧ ∃ ψ : EuclideanSpace ℂ (m × n),
      ‖ψ‖ = 1 ∧ ‖φ - ψ‖ ^ 2 ≤ 2 * δ / μ ^ 2 ∧
      Matrix.schmidtRank (WithLp.ofLp ψ) ≤ D * R ∧
      ∃ θ : ℝ, ψ = Complex.exp (θ * Complex.I) •
        ((‖Matrix.toEuclideanLin K ξ‖ : ℂ)⁻¹ • Matrix.toEuclideanLin K ξ) := by
  let a := ⟪φ, ξ⟫_ℂ
  let v := ξ - a • φ
  have hv : ⟪φ, v⟫_ℂ = 0 := inner_sub_inner_smul_unit_eq_zero φ ξ hφ
  have hdec : ξ = a • φ + v := by dsimp only [v]; abel
  have ha : a ≠ 0 := by
    intro hz
    have h := hμ.trans_le hoverlap
    change 0 < ‖a‖ at h
    rw [hz, norm_zero] at h
    exact (lt_irrefl 0) h
  have hvnorm : ‖v‖ ^ 2 ≤ 1 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ)
      (a • φ) v (by simp only [inner_smul_left, hv, mul_zero])
    rw [← hdec, hξ] at h
    nlinarith [sq_nonneg ‖a • φ‖]
  obtain ⟨hKvorth, hKvnorm⟩ := Matrix.perpendicular_shrinking_homogeneous
    (Matrix.toEuclideanLin K) φ δ hperp v hv
  have hKdec : Matrix.toEuclideanLin K ξ = a • φ + Matrix.toEuclideanLin K v := by
    rw [hdec, map_add, map_smul, hfix]
  obtain ⟨hne, θ, hunit, herror⟩ := exists_phase_normalized_of_decomposition
    φ (Matrix.toEuclideanLin K ξ) (Matrix.toEuclideanLin K v) a hφ ha hKvorth hKdec
  let ψ := Complex.exp (θ * Complex.I) •
    ((‖Matrix.toEuclideanLin K ξ‖ : ℂ)⁻¹ • Matrix.toEuclideanLin K ξ)
  refine ⟨hne, ψ, hunit, herror.trans ?_, ?_, θ, rfl⟩
  · calc
      _ ≤ 2 * δ / ‖a‖ ^ 2 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hKvnorm.trans (by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hvnorm hδ)) (by norm_num))
        (sq_nonneg _)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hμ)
        (pow_le_pow_left₀ hμ.le hoverlap 2)
  · rw [schmidtRank_phase_normalized_eq _ hne θ]
    exact (Matrix.schmidtRank_mulVec_le K (WithLp.ofLp ξ)).trans (Nat.mul_le_mul hD hR)

/-- A seed of overlap at least seven eighths gives norm error `exp(-x)`
when the squared shrinking factor has the corresponding explicit budget.
The rank is the actual filtered rank, at most the product of the two
supplied bounds. AKLV, Lemma 7.1, the accuracy-dependent filtering step. -/
theorem exists_filtered_approximation_of_seven_eighths
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (K : Matrix (m × n) (m × n) ℂ) (φ ξ : EuclideanSpace ℂ (m × n))
    (hφ : ‖φ‖ = 1) (hξ : ‖ξ‖ = 1) (hfix : Matrix.toEuclideanLin K φ = φ)
    (δ x : ℝ) (hδ : 0 ≤ δ) (hoverlap : (7 / 8 : ℝ) ≤ ‖⟪φ, ξ⟫_ℂ‖)
    (hbudget : δ ≤ (49 / 128) * Real.exp (-2 * x))
    (hperp : ∀ v : EuclideanSpace ℂ (m × n), ‖v‖ = 1 → ⟪φ, v⟫_ℂ = 0 →
      ⟪φ, Matrix.toEuclideanLin K v⟫_ℂ = 0 ∧ ‖Matrix.toEuclideanLin K v‖ ^ 2 ≤ δ)
    (D R : ℕ) (hD : Matrix.operatorSchmidtRank K ≤ D)
    (hR : Matrix.schmidtRank (WithLp.ofLp ξ) ≤ R) :
    Matrix.toEuclideanLin K ξ ≠ 0 ∧ ∃ ψ : EuclideanSpace ℂ (m × n),
      ‖ψ‖ = 1 ∧ ‖φ - ψ‖ ≤ Real.exp (-x) ∧
      Matrix.schmidtRank (WithLp.ofLp ψ) ≤ D * R ∧
      ∃ θ : ℝ, ψ = Complex.exp (θ * Complex.I) •
        ((‖Matrix.toEuclideanLin K ξ‖ : ℂ)⁻¹ • Matrix.toEuclideanLin K ξ) := by
  obtain ⟨hne, ψ, hunit, herror, hrank, hphase⟩ :=
    exists_filtered_approximation_of_overlap K φ ξ hφ hξ hfix (7 / 8) δ
      (by norm_num) hδ hoverlap hperp D R hD hR
  refine ⟨hne, ψ, hunit, ?_, hrank, hphase⟩
  have hexp : Real.exp (-2 * x) = Real.exp (-x) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp] at hbudget
  norm_num at herror
  nlinarith [Real.exp_pos (-x), norm_nonneg (φ - ψ)]

end TNLean.MPS.AreaLaw.AKLV

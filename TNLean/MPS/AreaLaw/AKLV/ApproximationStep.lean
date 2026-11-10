/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.ProductOverlapBootstrap
import TNLean.MPS.AreaLaw.AKLV.NormalizedVector

/-!
# Normalized approximate-projector steps

An operator fixing a unit target and shrinking its orthogonal complement
improves a nearby unit vector after normalization and a phase correction.
This is the changing-target step in AKLV, arXiv:1301.1162v1,
Lemma 6.3 (`l:5`, lines 1033–1052).
The phase is explicit because normalization alone preserves the phase
of the input's target component.
-/

open scoped InnerProductSpace

noncomputable section

namespace TNLean.MPS.AreaLaw.AKLV

/-- A normalized approximate-projector step reduces squared distance by at
most four times its squared shrinking factor, allowing a unit complex phase.
AKLV, Lemma 6.3. This auxiliary assumes the operator estimates explicitly;
it does not assert their existence for a Hamiltonian. -/
theorem exists_normalized_approximation_step
    {ι : Type*} [Fintype ι]
    (K : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)
    (φ ψ : EuclideanSpace ℂ ι) (hφ : ‖φ‖ = 1) (hψ : ‖ψ‖ = 1)
    (hfix : K φ = φ) (δ r : ℝ) (hδ : 0 ≤ δ)
    (hperp : ∀ v : EuclideanSpace ℂ ι, ‖v‖ = 1 → ⟪φ, v⟫_ℂ = 0 →
      ⟪φ, K v⟫_ℂ = 0 ∧ ‖K v‖ ^ 2 ≤ δ)
    (hr : r ≤ 1 / 2) (hclose : ‖φ - ψ‖ ^ 2 ≤ r) :
    K ψ ≠ 0 ∧ ∃ θ : ℝ,
      let χ := Complex.exp (θ * Complex.I) • ((‖K ψ‖ : ℂ)⁻¹ • K ψ)
      ‖χ‖ = 1 ∧ ‖φ - χ‖ ^ 2 ≤ 4 * δ * r := by
  let a : ℂ := ⟪φ, ψ⟫_ℂ
  let v := ψ - a • φ
  have hv : ⟪φ, v⟫_ℂ = 0 := inner_sub_inner_smul_unit_eq_zero φ ψ hφ
  have hdec : ψ = a • φ + v := by dsimp only [v]; abel
  have ha1 : ‖a‖ ≤ 1 := by
    simpa only [a, hφ, hψ, one_mul] using norm_inner_le_norm (𝕜 := ℂ) φ ψ
  have ham : 2 - 2 * ‖a‖ ≤ r := by
    have h := norm_sq_add_norm_sq_sub_le_norm_sub_exp_smul_sq φ ψ 0
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul,
      hφ, hψ, one_pow] at h
    simpa only [a, ← one_add_one_eq_two] using h.trans hclose
  have ha2 : 1 / 2 ≤ ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hvnorm : ‖a‖ ^ 2 + ‖v‖ ^ 2 = 1 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ)
      (a • φ) v (by simp only [inner_smul_left, hv, mul_zero])
    simpa only [← hdec, norm_smul, hφ, hψ, mul_one, one_pow, pow_two] using h.symm
  have hvr : ‖v‖ ^ 2 ≤ r := by nlinarith [sq_nonneg (1 - ‖a‖)]
  have hr0 : 0 ≤ r := (sq_nonneg _).trans hclose
  obtain ⟨hKvorth, hKvnorm⟩ :=
    Matrix.perpendicular_shrinking_homogeneous K φ δ hperp v hv
  have hKdec : K ψ = a • φ + K v := by rw [hdec, map_add, map_smul, hfix]
  have ha : a ≠ 0 := by
    intro hz
    simp only [hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at ha2
    norm_num at ha2
  obtain ⟨hne, θ, hunit, herror⟩ := exists_phase_normalized_of_decomposition
    φ (K ψ) (K v) a hφ ha hKvorth hKdec
  refine ⟨hne, θ, hunit, herror.trans ?_⟩
  apply (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr ha))).mpr
  have hb : ‖K v‖ ^ 2 ≤ δ * r :=
    hKvnorm.trans (mul_le_mul_of_nonneg_left hvr hδ)
  have hm := mul_le_mul_of_nonneg_left ha2 (mul_nonneg hδ hr0)
  nlinarith only [hb, hm]

end TNLean.MPS.AreaLaw.AKLV

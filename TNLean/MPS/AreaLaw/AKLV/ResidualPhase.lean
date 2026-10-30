/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.CodimensionOneGap
import QICLean.Analysis.DetectabilityLemma

/-!
# Phase alignment from an approximate eigenvector below the excited spectrum

The absolute excited-energy lower bound controls the orthogonal component
of an approximate eigenvector. This is the approximate-eigenvector step in
AKLV, arXiv:1301.1162v1, Section 6.3, closing the proof of Theorem 6.1(b).
-/

open Complex
open scoped InnerProductSpace

noncomputable section

/-- A residual below the absolute excited threshold controls the component
orthogonal to the actual ground vector. Auxiliary to AKLV, Theorem 6.1(b). -/
theorem norm_orthogonal_component_le_residual {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (K : E →L[ℂ] E) (hK : K.IsSymmetric) (φ : E) (hφ : ‖φ‖ = 1)
    (e' e a : ℝ) (heig : K φ = (e' : ℂ) • φ) (hea : e < a)
    (horth : ∀ w : E, ⟪φ, w⟫_ℂ = 0 → a * ‖w‖ ^ 2 ≤ (⟪w, K w⟫_ℂ).re)
    (z : E) :
    ‖z - ⟪φ, z⟫_ℂ • φ‖ ≤ ‖K z - (e : ℂ) • z‖ / (a - e) := by
  let P : E →L[ℂ] E := 1 - InnerProductSpace.rankOne ℂ φ φ
  have hP : IsStarProjection P :=
    (InnerProductSpace.isStarProjection_rankOne_self (𝕜 := ℂ) hφ).one_sub
  have hPapply (x : E) : P x = x - ⟪φ, x⟫_ℂ • φ := rfl
  have hself : ⟪φ, φ⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hφ]; simp
  have hinner (x : E) : ⟪φ, K x⟫_ℂ = (e' : ℂ) * ⟪φ, x⟫_ℂ := by
    have hsym : ⟪K φ, x⟫_ℂ = ⟪φ, K x⟫_ℂ := hK φ x
    rw [heig, inner_smul_left, conj_ofReal] at hsym
    exact hsym.symm
  have hcomm (x : E) : K (P x) = P (K x) := by
    simp only [hPapply, map_sub, map_smul, heig, hinner, smul_smul]
    rw [mul_comm]
  let w := P z
  have hw : ⟪φ, w⟫_ℂ = 0 := by
    rw [show w = P z from rfl, hPapply, inner_sub_right, inner_smul_right,
      hself, mul_one, sub_self]
  have hres : K w - (e : ℂ) • w = P (K z - (e : ℂ) • z) := by
    rw [show w = P z from rfl, hcomm, map_sub, map_smul]
  have hlow : (a - e) * ‖w‖ ^ 2 ≤ (⟪w, K w - (e : ℂ) • w⟫_ℂ).re := by
    have h := horth w hw
    have hselfw : (⟪w, w⟫_ℂ).re = ‖w‖ ^ 2 := by
      simpa only [RCLike.re_to_complex] using inner_self_eq_norm_sq (𝕜 := ℂ) w
    rw [inner_sub_right, inner_smul_right, Complex.sub_re, re_ofReal_mul, hselfw]
    nlinarith
  have hupper : (⟪w, K w - (e : ℂ) • w⟫_ℂ).re ≤
      ‖w‖ * ‖K z - (e : ℂ) • z‖ := by
    calc
      _ ≤ ‖w‖ * ‖K w - (e : ℂ) • w‖ := re_inner_le_norm (𝕜 := ℂ) _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (by
        rw [hres]
        exact ContinuousLinearMap.IsStarProjection.norm_apply_le hP _) (norm_nonneg _)
  have hden : 0 < a - e := sub_pos.mpr hea
  change ‖w‖ ≤ _
  by_cases hw0 : ‖w‖ = 0
  · rw [hw0]
    exact div_nonneg (norm_nonneg _) hden.le
  apply (le_div_iff₀ hden).mpr
  have hmul : ‖w‖ * ((a - e) * ‖w‖) ≤ ‖w‖ * ‖K z - (e : ℂ) • z‖ := by
    nlinarith
  have h := le_of_mul_le_mul_left hmul (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw0))
  nlinarith

/-- An approximate eigenvector and its distance to a unit target give a
phase-aligned squared-distance estimate for the actual ground vector.
No closeness of the ground vectors is assumed. AKLV, Theorem 6.1(b). -/
theorem exists_phase_sq_distance_le_residual {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (K : E →L[ℂ] E) (hK : K.IsSymmetric) (φ Ω : E)
    (hφ : ‖φ‖ = 1) (hΩ : ‖Ω‖ = 1)
    (e' e a : ℝ) (heig : K φ = (e' : ℂ) • φ) (hea : e < a)
    (horth : ∀ w : E, ⟪φ, w⟫_ℂ = 0 → a * ‖w‖ ^ 2 ≤ (⟪w, K w⟫_ℂ).re)
    (z : E) :
    ∃ θ : ℝ, ‖Ω - exp (θ * I) • φ‖ ^ 2 ≤
      2 * (‖K z - (e : ℂ) • z‖ / (a - e) + ‖Ω - z‖) ^ 2 := by
  let P : E →L[ℂ] E := 1 - InnerProductSpace.rankOne ℂ φ φ
  have hP : IsStarProjection P :=
    (InnerProductSpace.isStarProjection_rankOne_self (𝕜 := ℂ) hφ).one_sub
  have hPapply (x : E) : P x = x - ⟪φ, x⟫_ℂ • φ := rfl
  have hnorm : ‖P Ω‖ ≤ ‖K z - (e : ℂ) • z‖ / (a - e) + ‖Ω - z‖ := by
    have hsplit : P Ω = P z + P (Ω - z) := by rw [map_sub]; abel
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add
      (norm_orthogonal_component_le_residual K hK φ hφ e' e a heig hea horth z)
      (ContinuousLinearMap.IsStarProjection.norm_apply_le hP _))
  have hdeficit : 1 - ‖⟪φ, Ω⟫_ℂ‖ ^ 2 = ‖P Ω‖ ^ 2 := by
    have h := ContinuousLinearMap.IsStarProjection.norm_sq_eq
      (InnerProductSpace.isStarProjection_rankOne_self (𝕜 := ℂ) hφ) Ω
    simp only [hΩ, one_pow, InnerProductSpace.rankOne_apply, norm_smul, hφ, mul_one] at h
    change 1 = ‖⟪φ, Ω⟫_ℂ‖ ^ 2 + ‖P Ω‖ ^ 2 at h
    linarith
  have hbound : 1 * (1 - ‖⟪φ, Ω⟫_ℂ‖ ^ 2) ≤
      (‖K z - (e : ℂ) • z‖ / (a - e) + ‖Ω - z‖) ^ 2 := by
    rw [one_mul, hdeficit]
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  obtain ⟨θ, _, hθ⟩ := exists_isMinOn_sq_norm_sub_exp_smul_le_of_gap
    (by norm_num : (0 : ℝ) < 1) hΩ hφ hbound
  exact ⟨θ, by simpa only [div_one] using hθ⟩

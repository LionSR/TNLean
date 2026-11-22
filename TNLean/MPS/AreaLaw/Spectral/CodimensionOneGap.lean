/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Spectral.Perturbation.GapPerturbation
import QICLean.Analysis.Projection.DetectabilityLemma

/-!
# A spectral gap from a lower bound on one orthogonal complement

The min--max argument in AKLV, arXiv:1301.1162v1, Theorem 6.1(a),
needs only a quadratic lower bound on the original ground vector's
orthogonal complement. The minimizing vector of the new Hamiltonian
then has an actual spectral gap; no spectral separation of that new
Hamiltonian is supplied as an assumption.

## Phase alignment from an approximate eigenvector below the excited spectrum

The absolute excited-energy lower bound controls the orthogonal component
of an approximate eigenvector. This is the approximate-eigenvector step in
AKLV, arXiv:1301.1162v1, Section 6.3, closing the proof of Theorem 6.1(b).
-/

section

open Complex
open scoped InnerProductSpace

noncomputable section

/-- A homogeneous quadratic lower bound follows from the unit-vector
bound. Auxiliary to the min--max step of AKLV, Theorem 6.1(a). -/
theorem re_inner_lower_of_unit_orthogonal_lower {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (K : E →L[ℂ] E) (Ω : E) (a : ℝ)
    (h : ∀ x : E, ‖x‖ = 1 → ⟪Ω, x⟫_ℂ = 0 → a ≤ (⟪x, K x⟫_ℂ).re) :
    ∀ x : E, ⟪Ω, x⟫_ℂ = 0 → a * ‖x‖ ^ 2 ≤ (⟪x, K x⟫_ℂ).re := by
  intro x hx
  by_cases hx0 : x = 0
  · simp [hx0]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
  let y := ((‖x‖⁻¹ : ℝ) : ℂ) • x
  have hy : ‖y‖ = 1 := by simp [y, norm_smul, hn]
  have horth : ⟪Ω, y⟫_ℂ = 0 := by
    change ⟪Ω, ((‖x‖⁻¹ : ℝ) : ℂ) • x⟫_ℂ = 0
    rw [inner_smul_right, hx, mul_zero]
  have hlow := h y hy horth
  have hscale : (⟪y, K y⟫_ℂ).re = (‖x‖⁻¹) ^ 2 * (⟪x, K x⟫_ℂ).re := by
    rw [show y = ((‖x‖⁻¹ : ℝ) : ℂ) • x from rfl, map_smul, inner_smul_left,
      inner_smul_right, conj_ofReal, ← mul_assoc, ← ofReal_mul, re_ofReal_mul, sq]
  rw [hscale] at hlow
  have hmul := mul_le_mul_of_nonneg_right hlow (sq_nonneg ‖x‖)
  calc
    _ ≤ ((‖x‖⁻¹) ^ 2 * (⟪x, K x⟫_ℂ).re) * ‖x‖ ^ 2 := hmul
    _ = _ := by field_simp

/-- A codimension-one quadratic lower bound separates the actual lowest
eigenvector from all excited directions. This is the min--max step in
AKLV, arXiv:1301.1162v1, Theorem 6.1(a). The conclusion retains the
absolute excited-energy threshold `a`, useful for the residual estimate
in part (b). -/
theorem exists_ground_gap_of_orthogonal_lower {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (K : E →L[ℂ] E) (hK : K.IsPositive) (Ω : E) (hΩ : ‖Ω‖ = 1)
    (e a : ℝ) (hea : e < a) (htest : (⟪Ω, K Ω⟫_ℂ).re ≤ e)
    (horth : ∀ x : E, ⟪Ω, x⟫_ℂ = 0 → a * ‖x‖ ^ 2 ≤ (⟪x, K x⟫_ℂ).re) :
    ∃ (e' : ℝ) (φ : E), ‖φ‖ = 1 ∧ K φ = (e' : ℂ) • φ ∧ 0 ≤ e' ∧ e' ≤ e ∧
      (∀ x : E, (a - e') * (‖x‖ ^ 2 - ‖⟪φ, x⟫_ℂ‖ ^ 2) ≤
        (⟪x, K x⟫_ℂ).re - e' * ‖x‖ ^ 2) ∧
      (∀ x : E, ⟪φ, x⟫_ℂ = 0 → a * ‖x‖ ^ 2 ≤ (⟪x, K x⟫_ℂ).re) := by
  have : Nontrivial E := ⟨⟨Ω, 0, fun h ↦ by simp [h] at hΩ⟩⟩
  obtain ⟨φ, hφ, heig, hmin⟩ := exists_unit_eigenvector_re_inner_le hK.isSymmetric
  let e' := (⟪φ, K φ⟫_ℂ).re
  have he'0 : 0 ≤ e' := hK.re_inner_nonneg_right φ
  have he'e : e' ≤ e := by
    have h := (hmin Ω).trans htest
    simpa only [hΩ, one_pow, mul_one] using h
  have hβ : ⟪Ω, φ⟫_ℂ ≠ 0 := by
    intro hz
    have h := horth φ hz
    rw [hφ, one_pow, mul_one] at h
    exact (not_le_of_gt (hea.trans_le' he'e)) h
  have hφorth : ∀ x : E, ⟪φ, x⟫_ℂ = 0 → a * ‖x‖ ^ 2 ≤ (⟪x, K x⟫_ℂ).re := by
    intro x hx
    let α := ⟪Ω, x⟫_ℂ
    let β := ⟪Ω, φ⟫_ℂ
    let y := (-α) • φ + β • x
    have hxy : ⟪φ, β • x⟫_ℂ = 0 := by rw [inner_smul_right, hx, mul_zero]
    have hy : ⟪Ω, y⟫_ℂ = 0 := by
      dsimp [y, α, β]
      rw [inner_add_right, inner_smul_right, inner_smul_right]
      ring
    have hyn : ‖y‖ ^ 2 = ‖α‖ ^ 2 + ‖β‖ ^ 2 * ‖x‖ ^ 2 := by
      have hi : ⟪(-α) • φ, β • x⟫_ℂ = 0 := by rw [inner_smul_left, hxy, mul_zero]
      rw [show y = (-α) • φ + β • x from rfl, sq,
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hi,
        norm_smul, norm_smul, hφ, norm_neg]
      ring
    have hyK : (⟪y, K y⟫_ℂ).re = ‖α‖ ^ 2 * e' + ‖β‖ ^ 2 * (⟪x, K x⟫_ℂ).re := by
      rw [show y = (-α) • φ + β • x from rfl,
        re_inner_smul_add_eigenvector hK.isSymmetric hφ heig hxy,
        norm_neg, map_smul, inner_smul_left, inner_smul_right,
        ← mul_assoc, mul_comm _ β, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      rw [← ofReal_pow, re_ofReal_mul]
    have hlower := horth y hy
    rw [hyn, hyK] at hlower
    have hα : ‖α‖ ^ 2 * e' ≤ ‖α‖ ^ 2 * a :=
      mul_le_mul_of_nonneg_left (he'e.trans hea.le) (sq_nonneg _)
    have hkey : ‖β‖ ^ 2 * (a * ‖x‖ ^ 2) ≤ ‖β‖ ^ 2 * (⟪x, K x⟫_ℂ).re := by
      nlinarith
    exact le_of_mul_le_mul_left hkey (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hβ))
  refine ⟨e', φ, hφ, heig, he'0, he'e, ?_, hφorth⟩
  intro x
  let α := ⟪φ, x⟫_ℂ
  let w := x - α • φ
  have hself : ⟪φ, φ⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hφ]; simp
  have hw : ⟪φ, w⟫_ℂ = 0 := by
    rw [show w = x - α • φ from rfl, inner_sub_right, inner_smul_right, hself, mul_one]
    exact sub_self _
  have hx : x = α • φ + w := by dsimp [w]; abel
  have hn : ‖x‖ ^ 2 = ‖α‖ ^ 2 + ‖w‖ ^ 2 := by
    have hi : ⟪α • φ, w⟫_ℂ = 0 := by rw [inner_smul_left, hw, mul_zero]
    conv_lhs => rw [hx]
    rw [sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hi, norm_smul, hφ]
    ring
  have hq : (⟪x, K x⟫_ℂ).re = ‖α‖ ^ 2 * e' + (⟪w, K w⟫_ℂ).re := by
    conv_lhs => rw [hx]
    exact re_inner_smul_add_eigenvector hK.isSymmetric hφ heig hw α
  have hlow := hφorth w hw
  rw [hn, hq]
  change (a - e') * (‖α‖ ^ 2 + ‖w‖ ^ 2 - ‖α‖ ^ 2) ≤ _
  nlinarith
end

end

section

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
end

end

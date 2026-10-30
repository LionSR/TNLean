/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.GapPerturbation

/-!
# A spectral gap from a lower bound on one orthogonal complement

The min--max argument in AKLV, arXiv:1301.1162v1, Theorem 6.1(a),
needs only a quadratic lower bound on the original ground vector's
orthogonal complement. The minimizing vector of the new Hamiltonian
then has an actual spectral gap; no spectral separation of that new
Hamiltonian is supplied as an assumption.
-/

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

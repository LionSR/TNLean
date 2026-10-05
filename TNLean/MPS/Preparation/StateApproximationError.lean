/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The normalized overlap error

The error of arXiv:2307.01696, eq. (1), is not a metric. The squared
phase-aligned distance gives the triangle bound used for circuit conversion.
These declarations are re-exported by `CircuitEquivalence`.
-/

open scoped ComplexOrder InnerProductSpace
namespace MPSPreparation

/-! ### The error `1 - |⟨x|y⟩|` -/

section Error

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- For unit vectors `a`, `b` and a unit scalar `c`, `1 - |⟨a|b⟩| ≤ ‖a - c b‖² / 2`. -/
theorem one_sub_norm_inner_le_norm_sub_smul_sq {a b : E} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    {c : ℂ} (hc : ‖c‖ = 1) : 1 - ‖⟪a, b⟫_ℂ‖ ≤ ‖a - c • b‖ ^ 2 / 2 := by
  rw [@norm_sub_sq ℂ, norm_smul, hc, ha, hb, inner_smul_right]
  have h1 := RCLike.re_le_norm (c * ⟪a, b⟫_ℂ)
  rw [norm_mul, hc, one_mul] at h1
  linarith

/-- For unit vectors `a`, `b` some unit multiple of `b` is at squared distance
`2 (1 - |⟨a|b⟩|)` from `a`. -/
theorem exists_norm_sub_smul_sq_eq {a b : E} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ‖a - c • b‖ ^ 2 = 2 * (1 - ‖⟪a, b⟫_ℂ‖) := by
  set z := ⟪a, b⟫_ℂ
  have key : ∀ c : ℂ, ‖c‖ = 1 → c * z = (‖z‖ : ℂ) →
      ‖a - c • b‖ ^ 2 = 2 * (1 - ‖z‖) := fun c hc hcz => by
    rw [@norm_sub_sq ℂ, norm_smul, hc, ha, hb, inner_smul_right]
    change 1 ^ 2 - 2 * RCLike.re (c * z) + (1 * 1) ^ 2 = _
    rw [hcz, RCLike.re_to_complex, Complex.ofReal_re]
    ring
  by_cases hz : z = 0
  · exact ⟨1, norm_one, key 1 norm_one (by simp [hz])⟩
  · have hz' : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
    have hc : ‖star z / (‖z‖ : ℂ)‖ = 1 := by
      rw [norm_div, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        div_self (norm_ne_zero_iff.mpr hz)]
    refine ⟨star z / ‖z‖, hc, key _ hc ?_⟩
    rw [div_mul_eq_mul_div, Complex.star_def, Complex.conj_mul', div_eq_iff hz']
    ring

/-- **The triangle step for the error.** For unit vectors `x`, `y`, `z`,
`1 - |⟨x|z⟩| ≤ 2 ((1 - |⟨x|y⟩|) + (1 - |⟨y|z⟩|))`. -/
theorem one_sub_norm_inner_le_two_mul_add {x y z : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hz : ‖z‖ = 1) :
    1 - ‖⟪x, z⟫_ℂ‖ ≤ 2 * ((1 - ‖⟪x, y⟫_ℂ‖) + (1 - ‖⟪y, z⟫_ℂ‖)) := by
  obtain ⟨c₁, hc₁, h₁⟩ := exists_norm_sub_smul_sq_eq hx hy
  obtain ⟨c₂, hc₂, h₂⟩ := exists_norm_sub_smul_sq_eq hy hz
  have hc : ‖c₁ * c₂‖ = 1 := by rw [norm_mul, hc₁, hc₂, one_mul]
  have htri : ‖x - (c₁ * c₂) • z‖ ≤ ‖x - c₁ • y‖ + ‖y - c₂ • z‖ := by
    calc ‖x - (c₁ * c₂) • z‖ = ‖(x - c₁ • y) + c₁ • (y - c₂ • z)‖ := by
          rw [smul_sub, mul_smul]; congr 1; abel
      _ ≤ ‖x - c₁ • y‖ + ‖c₁ • (y - c₂ • z)‖ := norm_add_le _ _
      _ = ‖x - c₁ • y‖ + ‖y - c₂ • z‖ := by rw [norm_smul, hc₁, one_mul]
  have h := one_sub_norm_inner_le_norm_sub_smul_sq hx hz hc
  have hsq : ‖x - (c₁ * c₂) • z‖ ^ 2 ≤ 2 * (‖x - c₁ • y‖ ^ 2 + ‖y - c₂ • z‖ ^ 2) := by
    nlinarith [norm_nonneg (x - (c₁ * c₂) • z), norm_nonneg (x - c₁ • y),
      norm_nonneg (y - c₂ • z), sq_nonneg (‖x - c₁ • y‖ - ‖y - c₂ • z‖)]
  rw [h₁, h₂] at hsq
  linarith

end Error

end MPSPreparation

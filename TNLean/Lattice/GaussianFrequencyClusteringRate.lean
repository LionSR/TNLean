/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.GaussianFilter.Kernel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# An exponential rate for the actual Gaussian frequency bound

The cutoff T=ℓ/(2v) balances the short-time propagation exponential and
the gap tail. The remaining square-root factor is bounded by ℓ, and
ℓ exp(-ℓ/2) is bounded by 4 exp(-ℓ/4). This gives one positive decay
rate depending only on the positive gap and propagation velocity.

Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3, the Gaussian
frequency-separation and propagation balance following Lemma 3.1.
-/

noncomputable section

open scoped NNReal

namespace GaussianFilter

/-- The actual normalization coefficient at inverse variance is a square
root, including zero variance. Source: Hastings–Koma,
arXiv:math-ph/0507008, Lemma 3.1, Gaussian normalization in equation (3.8). -/
theorem kernel_inv_zero_eq_sqrt (s : ℝ≥0) :
    kernel s⁻¹ 0 = Real.sqrt ((s : ℝ) / (2 * Real.pi)) := by
  rw [kernel_eq]
  simp only [zero_pow (by decide : 2 ≠ 0), neg_zero, zero_div, Real.exp_zero, mul_one]
  rw [NNReal.coe_inv, ← Real.sqrt_inv, mul_inv_rev, inv_inv, div_eq_mul_inv]

end GaussianFilter

namespace TNLean.Lattice

/-- The explicit frequency-separation bound has a uniform positive
exponential rate. The prefactor is linear in the nonnegative support
parameter, and neither a rate nor a decay estimate is supplied as a
premise. Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3,
Gaussian frequency separation with T=ℓ/(2v). -/
theorem exists_gaussianFrequencyClusteringRate
    (Δ v : ℝ) (hΔ : 0 < Δ) (hv : 0 < v) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ m : ℝ, 0 ≤ m → ∀ ℓ : ℝ, 1 ≤ ℓ →
      2 * Real.exp (-ℓ * Δ / (4 * v)) +
          Real.sqrt (ℓ / (4 * Real.pi * v * Δ)) *
            (2 * m * v * Real.exp (-ℓ / 2) +
              (4 * v / ℓ) * Real.exp (-ℓ * Δ / (4 * v))) ≤
        C * (m + 1) * Real.exp (-κ * ℓ) := by
  let a := Δ / (4 * v)
  let c := Real.sqrt (1 / (4 * Real.pi * v * Δ))
  let κ := min (1 / 4 : ℝ) (Δ / (8 * v))
  let C := 2 + 12 * c * v
  have ha : 0 < a := div_pos hΔ (by positivity)
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have hC : 0 < C := by dsimp only [C]; positivity
  have hκ : 0 < κ := lt_min (by norm_num) (div_pos hΔ (by positivity))
  have hκquarter : κ ≤ 1 / 4 := min_le_left _ _
  have hκa : κ ≤ a := by
    have hhalf : Δ / (8 * v) = a / 2 := by
      dsimp only [a]
      field_simp [hv.ne'] <;> ring
    exact (min_le_right _ _).trans (by rw [hhalf]; linarith)
  refine ⟨C, κ, hC, hκ, fun m hm ℓ hℓ ↦ ?_⟩
  have hℓpos : 0 < ℓ := lt_of_lt_of_le zero_lt_one hℓ
  have hsqrt : Real.sqrt ℓ ≤ ℓ := Real.sqrt_le_self_iff.mpr (Or.inr hℓ)
  have hquot : Real.sqrt ℓ / ℓ ≤ 1 := (div_le_one hℓpos).mpr hsqrt
  have hfactor : Real.sqrt (ℓ / (4 * Real.pi * v * Δ)) = c * Real.sqrt ℓ := by
    rw [show ℓ / (4 * Real.pi * v * Δ) =
      ℓ * (1 / (4 * Real.pi * v * Δ)) by ring, Real.sqrt_mul hℓpos.le]
    exact mul_comm _ _
  have htail : Real.exp (-ℓ * Δ / (4 * v)) ≤ Real.exp (-κ * ℓ) := by
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_right hκa hℓpos.le
    dsimp only [a] at hmul
    nlinarith
  have hquarter : Real.exp (-ℓ / 4) ≤ Real.exp (-κ * ℓ) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hκquarter hℓpos.le]
  have hlinear : ℓ ≤ 4 * Real.exp (ℓ / 4) := by
    have hexp := Real.add_one_le_exp (ℓ / 4)
    linarith
  have hhalf : ℓ * Real.exp (-ℓ / 2) ≤ 4 * Real.exp (-κ * ℓ) := by
    calc
      _ ≤ (4 * Real.exp (ℓ / 4)) * Real.exp (-ℓ / 2) :=
        mul_le_mul_of_nonneg_right hlinear (Real.exp_pos _).le
      _ = 4 * Real.exp (-ℓ / 4) := by
        rw [mul_assoc, ← Real.exp_add, show ℓ / 4 + -ℓ / 2 = -ℓ / 4 by ring]
      _ ≤ _ := mul_le_mul_of_nonneg_left hquarter (by norm_num)
  have hrootHalf : Real.sqrt ℓ * Real.exp (-ℓ / 2) ≤
      4 * Real.exp (-κ * ℓ) :=
    (mul_le_mul_of_nonneg_right hsqrt (Real.exp_pos _).le).trans hhalf
  have hrootTail : (Real.sqrt ℓ / ℓ) * Real.exp (-ℓ * Δ / (4 * v)) ≤
      Real.exp (-κ * ℓ) := by
    exact (mul_le_mul_of_nonneg_right hquot (Real.exp_pos _).le).trans
      (by simpa only [one_mul] using htail)
  rw [hfactor]
  calc
    _ = 2 * Real.exp (-ℓ * Δ / (4 * v)) +
        (2 * c * m * v) * (Real.sqrt ℓ * Real.exp (-ℓ / 2)) +
        (4 * c * v) * ((Real.sqrt ℓ / ℓ) * Real.exp (-ℓ * Δ / (4 * v))) := by ring
    _ ≤ 2 * Real.exp (-κ * ℓ) +
        (2 * c * m * v) * (4 * Real.exp (-κ * ℓ)) +
        (4 * c * v) * Real.exp (-κ * ℓ) := by
      exact add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left htail (by norm_num))
          (mul_le_mul_of_nonneg_left hrootHalf (by positivity)))
        (mul_le_mul_of_nonneg_left hrootTail (by positivity))
    _ = (2 + 8 * c * m * v + 4 * c * v) * Real.exp (-κ * ℓ) := by ring
    _ ≤ C * (m + 1) * Real.exp (-κ * ℓ) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      dsimp only [C]
      nlinarith [mul_nonneg hc hv.le, mul_nonneg (mul_nonneg hc hv.le) hm]

end TNLean.Lattice

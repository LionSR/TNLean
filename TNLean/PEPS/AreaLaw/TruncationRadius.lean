/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The base truncation radius

With the stretched exponent `1/2`, a truncation error `B s e^{-(c/2) √r₀}` for a set of
size `s ≤ C₀ n²` becomes at most `min {n^{-1000}, g/4}` once `r₀ = ⌈C₁ (log n)²⌉` with a
constant `C₁` chosen from `B, C₀, c, g` alone.

## Main results

* `TNLean.PEPS.AreaLaw.exists_truncationConstant`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  proof of Proposition 4.5 (`prop:truncation`), section file `03-quasilocal.tex`,
  lines 480–485. Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
  Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw

/-- `K / 2 ≤ 2^K` for `K ≥ 0`. -/
theorem half_le_two_rpow {K : ℝ} (hK : 0 ≤ K) : K / 2 ≤ (2 : ℝ) ^ K := by
  rw [Real.rpow_def_of_pos two_pos]
  have h1 := Real.add_one_le_exp (Real.log 2 * K)
  have h2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  nlinarith

/-- **Choice of the base radius** (`03-quasilocal.tex`, lines 480–485). For `B, C₀ ≥ 0`,
`c > 0` and `g > 0` there is `C₁ > 0` such that for every real `n ≥ 2` and every
`0 ≤ s ≤ C₀ n²`, with `r₀ = ⌈C₁ (log n)²⌉`,
`B s e^{-(c/2) √r₀} ≤ min {n^{-1000}, g / 4}`. -/
theorem exists_truncationConstant {B C₀ c g : ℝ} (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀) (hc : 0 < c)
    (hg : 0 < g) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ n : ℝ, 2 ≤ n → ∀ s : ℝ, 0 ≤ s → s ≤ C₀ * n ^ 2 →
      B * s * Real.exp (-(c / 2 * ((⌈C₁ * Real.log n ^ 2⌉₊ : ℕ) : ℝ) ^ (1 / 2 : ℝ))) ≤
        min (n ^ (-1000 : ℝ)) (g / 4) := by
  set m := min 1 (g / 4)
  have hm : 0 < m := lt_min one_pos (by positivity)
  set K := 2 * (B * C₀) / m
  have hK : 0 ≤ K := by positivity
  set β := 1002 + K
  set C₁ := (β / (c / 2)) ^ 2
  have hβ : 0 < β := by positivity
  refine ⟨C₁, by positivity, fun n hn s hs hsn => ?_⟩
  have hn0 : 0 < n := by linarith
  have hlog : 0 < Real.log n := Real.log_pos (by linarith)
  set r₀ : ℕ := ⌈C₁ * Real.log n ^ 2⌉₊
  -- `√r₀ ≥ (β / (c/2)) log n`.
  have hr : β / (c / 2) * Real.log n ≤ (r₀ : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    refine Real.le_sqrt_of_sq_le ?_
    calc ((β / (c / 2) * Real.log n) ^ 2 : ℝ) = C₁ * Real.log n ^ 2 := by
          simp only [C₁]; ring
      _ ≤ (r₀ : ℝ) := Nat.le_ceil _
  have hexp : Real.exp (-(c / 2 * (r₀ : ℝ) ^ (1 / 2 : ℝ))) ≤ n ^ (-β) := by
    rw [Real.rpow_def_of_pos hn0]
    refine Real.exp_le_exp.mpr ?_
    have := mul_le_mul_of_nonneg_left hr (by positivity : (0 : ℝ) ≤ c / 2)
    have heq : c / 2 * (β / (c / 2) * Real.log n) = β * Real.log n := by field_simp
    nlinarith
  -- `B s n^{-β} ≤ B C₀ n^{2-β} = B C₀ n^{-K} n^{-1000}`.
  have hbound : B * s * Real.exp (-(c / 2 * (r₀ : ℝ) ^ (1 / 2 : ℝ))) ≤
      B * C₀ * n ^ (-K) * n ^ (-1000 : ℝ) := by
    have hsplit : n ^ (2 : ℝ) * n ^ (-β) = n ^ (-K) * n ^ (-1000 : ℝ) := by
      rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]; congr 1; simp only [β]; ring
    calc B * s * Real.exp (-(c / 2 * (r₀ : ℝ) ^ (1 / 2 : ℝ)))
        ≤ B * (C₀ * n ^ 2) * n ^ (-β) := by gcongr
      _ = B * C₀ * (n ^ (2 : ℝ) * n ^ (-β)) := by rw [Real.rpow_two]; ring
      _ = B * C₀ * n ^ (-K) * n ^ (-1000 : ℝ) := by rw [hsplit]; ring
  -- `B C₀ n^{-K} ≤ B C₀ 2^{-K} ≤ m`.
  have hnK : n ^ (-K) ≤ (2 : ℝ) ^ (-K) :=
    Real.rpow_le_rpow_of_nonpos two_pos hn (by linarith)
  have h2K : B * C₀ * (2 : ℝ) ^ (-K) ≤ m := by
    have h1 : B * C₀ = m * (K / 2) := by simp only [K]; field_simp
    have h2 : B * C₀ ≤ m * (2 : ℝ) ^ K := by
      rw [h1]; exact mul_le_mul_of_nonneg_left (half_le_two_rpow hK) hm.le
    rw [Real.rpow_neg two_pos.le, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    linarith
  have hBnK : B * C₀ * n ^ (-K) ≤ m :=
    (mul_le_mul_of_nonneg_left hnK (by positivity)).trans h2K
  have hn1000 : n ^ (-1000 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hpos : 0 ≤ n ^ (-1000 : ℝ) := Real.rpow_nonneg hn0.le _
  refine le_min ?_ ?_
  · calc _ ≤ B * C₀ * n ^ (-K) * n ^ (-1000 : ℝ) := hbound
      _ ≤ 1 * n ^ (-1000 : ℝ) := by
          gcongr; exact hBnK.trans (min_le_left _ _)
      _ = n ^ (-1000 : ℝ) := one_mul _
  · calc _ ≤ B * C₀ * n ^ (-K) * n ^ (-1000 : ℝ) := hbound
      _ ≤ (g / 4) * 1 := by
          gcongr
          · exact hBnK.trans (min_le_right _ _)
      _ = g / 4 := mul_one _

end TNLean.PEPS.AreaLaw

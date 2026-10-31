/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Absorbing the snake truncation window

The square has `L²` sites. At accuracy `1/L`, the sequential truncation window
contains `log (2 L³ b)`, where `b` is the square root of the tail prefactor.
The inequality `log L ≤ 2 √L` bounds this window by a constant times `L`.

Source: the one-dimensional note, `part2a_mps_information.tex`,
`sec:shortcut`, proof of `thm:Bshort`, lines 73–92, applied to the square-grid
snake ordering.
-/

namespace TNLean.MPS.AreaLaw

/-- The square-grid concentration window grows at most linearly with the side
length, uniformly for `L ≥ 2`. The constants `a` and `b` are independent of `L`.
Source: the threshold argument in `part2a_mps_information.tex`, `thm:Bshort`. -/
theorem snakeGrid_window_le_linear {a b l : ℝ} (ha : 0 ≤ a) (hb : 1 ≤ b)
    (hl : 2 ≤ l) :
    Real.sqrt (a * (l + 2)) * Real.log (2 * l ^ 3 * b) ≤
      Real.sqrt (2 * a) * (Real.log (2 * b) + 6) * l := by
  have hl0 : 0 < l := by linarith
  have hl1 : 1 ≤ l := by linarith
  have hb0 : 0 < b := by linarith
  have hlog : Real.log l ≤ 2 * Real.sqrt l := by
    have h := Real.log_le_rpow_div hl0.le (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h
    linarith
  have hlogb : 0 ≤ Real.log (2 * b) := Real.log_nonneg (by linarith)
  have hsqrt : Real.sqrt (a * (l + 2)) ≤ Real.sqrt (2 * a) * Real.sqrt l := by
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    nlinarith
  have hlogs : Real.log (2 * l ^ 3 * b) = Real.log (2 * b) + 3 * Real.log l := by
    rw [show 2 * l ^ 3 * b = (2 * b) * l ^ 3 by ring,
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    norm_num
  rw [hlogs]
  have hlogl : 0 ≤ Real.log l := Real.log_nonneg hl1
  have hlroot : Real.sqrt l ≤ l := (Real.sqrt_le_left hl0.le).mpr (by nlinarith)
  have hsq : Real.sqrt l ^ 2 = l := Real.sq_sqrt hl0.le
  calc
    Real.sqrt (a * (l + 2)) * (Real.log (2 * b) + 3 * Real.log l)
        ≤ (Real.sqrt (2 * a) * Real.sqrt l) *
            (Real.log (2 * b) + 6 * Real.sqrt l) := by
          exact mul_le_mul hsqrt (by linarith) (by positivity) (by positivity)
    _ = Real.sqrt (2 * a) * (Real.log (2 * b) * Real.sqrt l + 6 * l) := by
      rw [← hsq]
      rw [Real.sqrt_sq (Real.sqrt_nonneg l)]
      ring
    _ ≤ Real.sqrt (2 * a) * (Real.log (2 * b) + 6) * l := by
      have ht := mul_le_mul_of_nonneg_left hlroot hlogb
      calc
        _ ≤ Real.sqrt (2 * a) * (Real.log (2 * b) * l + 6 * l) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)
        _ = _ := by ring

end TNLean.MPS.AreaLaw

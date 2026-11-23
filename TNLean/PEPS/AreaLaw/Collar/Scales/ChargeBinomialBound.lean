/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Ring

/-!
# The binomial factor in finite charge-path bounds

The factorial in the binomial bound is retained and cancelled against the
length-dependent time window. The exponential series at `j` gives
`j^j / j! ≤ e^j`, and hence `choose(v,j) ≤ (ev/j)^j`. This converts
a time window of size at most `Cj` and a per-step weight `a` into `(eCa)^j`.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 310–325, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

/-- The factorial term gives the binomial estimate used for distinct charge
times. `08-scanner.tex`, lines 318–321. -/
theorem choose_le_exp_mul_div_pow (v j : ℕ) (hj : 0 < j) :
    (v.choose j : ℝ) ≤ (Real.exp 1 * v / j) ^ j := by
  have hj0 : (j : ℝ) ≠ 0 := by positivity
  have hfactorial := Real.pow_div_factorial_le_exp (j : ℝ) (Nat.cast_nonneg j) j
  have hexp : Real.exp (j : ℝ) = Real.exp 1 ^ j := by
    simpa using Real.exp_nat_mul 1 j
  rw [hexp] at hfactorial
  calc
    (v.choose j : ℝ) ≤ (v : ℝ) ^ j / j.factorial := Nat.choose_le_pow_div j v
    _ = ((v : ℝ) / j) ^ j * ((j : ℝ) ^ j / j.factorial) := by
      symm
      rw [div_pow, ← mul_div_assoc, div_mul_cancel₀ _ (pow_ne_zero _ hj0)]
    _ ≤ ((v : ℝ) / j) ^ j * Real.exp 1 ^ j :=
      mul_le_mul_of_nonneg_left hfactorial (by positivity)
    _ = (Real.exp 1 * v / j) ^ j := by
      rw [← mul_pow]
      congr 1
      ring

/-- A length-proportional time window and a nonnegative per-step weight have
one length-independent exponential ratio. This retains the factorial saving
from choosing distinct times. `08-scanner.tex`, lines 310–325. -/
theorem choose_mul_pow_le_of_window_bound (v j : ℕ) (hj : 0 < j)
    (a C : ℝ) (ha : 0 ≤ a) (hwindow : (v : ℝ) ≤ C * j) :
    (v.choose j : ℝ) * a ^ j ≤ (Real.exp 1 * C * a) ^ j := by
  have hjpos : (0 : ℝ) < j := by positivity
  have hbase : Real.exp 1 * v / j ≤ Real.exp 1 * C := by
    apply (div_le_iff₀ hjpos).mpr
    calc
      Real.exp 1 * v ≤ Real.exp 1 * (C * j) :=
        mul_le_mul_of_nonneg_left hwindow (Real.exp_pos 1).le
      _ = Real.exp 1 * C * j := by ring
  calc
    (v.choose j : ℝ) * a ^ j ≤ (Real.exp 1 * v / j) ^ j * a ^ j :=
      mul_le_mul_of_nonneg_right (choose_le_exp_mul_div_pow v j hj) (pow_nonneg ha _)
    _ = (Real.exp 1 * v / j * a) ^ j := (mul_pow _ _ _).symm
    _ ≤ (Real.exp 1 * C * a) ^ j :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hbase ha) _

end TNLean.PEPS.AreaLaw.Scan

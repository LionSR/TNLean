/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Cost estimates for a recursion with a fixed number of child calls

A recurrence `T (j + 1) ≤ r * T j + C` with `r ≥ 2` gives
`T L ≤ (a + C) * r ^ L - C` when `T 0 ≤ a` and `C ≥ 0`.
For the balanced rank-two MPU construction, six child calls correspond to
`r = 6` and `N = 2 ^ L`. The construction is described separately in
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Theorem 6.
This module proves only the numerical implication from the recurrence.
-/

namespace MPUCircuit

/-- Constant overhead at each node of an `r`-branching recursion is absorbed
by a multiple of `r ^ L`. The assumed recurrence is numerical and does not
assert existence of a circuit. -/
theorem cost_le_pow_of_constant_branching (T : ℕ → ℝ) (a C r : ℝ) (hC : 0 ≤ C) (hr : 2 ≤ r)
    (hbase : T 0 ≤ a) (hstep : ∀ j, T (j + 1) ≤ r * T j + C) (L : ℕ) :
    T L ≤ (a + C) * r ^ L - C := by
  induction L with
  | zero => simpa using hbase
  | succ L ih =>
    have hr₀ : 0 ≤ r := le_trans (by norm_num) hr
    refine (hstep L).trans ?_
    calc
      _ ≤ r * ((a + C) * r ^ L - C) + C :=
        add_le_add (mul_le_mul_of_nonneg_left ih hr₀) le_rfl
      _ ≤ (a + C) * r ^ (L + 1) - C := by
        rw [pow_succ]
        nlinarith [mul_nonneg (sub_nonneg.mpr hr) hC]

end MPUCircuit

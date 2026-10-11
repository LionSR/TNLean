/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ChargeBinomialBound

/-!
# Regression tests for the factorial saving in charge-time choices

The time-window bound cancels the path length before any asymptotic argument.
-/

set_option autoImplicit false

open TNLean.PEPS.AreaLaw.Scan

example (v j n r : ℕ) (hj : 0 < j) (a : ℝ) (ha : 0 ≤ a)
    (hv : v ≤ 9 * n * r * j) :
    (v.choose j : ℝ) * a ^ j ≤ (Real.exp 1 * (9 * n * r) * a) ^ j := by
  apply choose_mul_pow_le_of_window_bound v j hj a (9 * n * r) ha
  exact_mod_cast hv

-- With no available time slots, the same positive-length inequality still applies.
example (j : ℕ) (hj : 0 < j) :
    (Nat.choose 0 j : ℝ) ≤ (Real.exp 1 * 0 / j) ^ j := by
  simpa using choose_le_exp_mul_div_pow 0 j hj

set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.AreaLaw.Scan.choose_le_exp_mul_div_pow'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms choose_le_exp_mul_div_pow

/--
info: 'TNLean.PEPS.AreaLaw.Scan.choose_mul_pow_le_of_window_bound'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms choose_mul_pow_le_of_window_bound

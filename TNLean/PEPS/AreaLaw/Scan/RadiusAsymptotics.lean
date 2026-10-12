/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Positivity

/-!
# The rounded logarithmic splitting radius

The splitting radius `⌈C log² n⌉` and every fixed multiple of its cube grow more
slowly than every positive power of `n`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24,
  2026, `08-scanner.tex`, splitting radius and bad-history estimate.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open Filter Asymptotics

namespace TNLean.PEPS.AreaLaw.Scan

/-- The rounded splitting radius from `08-scanner.tex`, line 49. -/
def roundedLogRadius (C : ℝ) (n : ℕ) : ℕ :=
  ⌈C * (Real.log n) ^ 2⌉₊

/-- Rounding the source's squared-logarithmic radius preserves its decay relative
to every positive power, as used in the bad-history estimate of `08-scanner.tex`. -/
theorem isLittleO_roundedLogRadius_rpow {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) :
    (fun n : ℕ => (roundedLogRadius C n : ℝ)) =o[atTop]
      fun n => (n : ℝ) ^ ε := by
  have hlog : (fun n : ℕ => C * (Real.log n) ^ 2) =o[atTop]
      fun n => (n : ℝ) ^ ε := by
    simpa only [Real.rpow_two] using
      (isLittleO_log_rpow_rpow_atTop 2 hε).natCast_atTop.const_mul_left C
  have hone : (fun _ : ℕ => (1 : ℝ)) =o[atTop] fun n => (n : ℝ) ^ ε :=
    ((isLittleO_const_id_atTop (1 : ℝ)).comp_tendsto
      (tendsto_rpow_atTop hε)).natCast_atTop
  refine (IsBigO.of_norm_eventuallyLE (Eventually.of_forall fun n => ?_)).trans_isLittleO
    (hlog.add hone)
  change ‖(roundedLogRadius C n : ℝ)‖ ≤ C * (Real.log n) ^ 2 + 1
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact (Nat.ceil_lt_add_one (mul_nonneg hC (sq_nonneg _))).le

/-- Every fixed multiple of the source radius is eventually below any positive
power, as required for the cutoffs in `08-scanner.tex`. -/
theorem eventually_const_mul_roundedLogRadius_le_rpow {C ε : ℝ}
    (hC : 0 ≤ C) (hε : 0 < ε) (A : ℝ) :
    ∀ᶠ n : ℕ in atTop, A * (roundedLogRadius C n : ℝ) ≤ (n : ℝ) ^ ε := by
  filter_upwards [((isLittleO_roundedLogRadius_rpow hC hε).const_mul_left A).bound
    (show (0 : ℝ) < 1 from zero_lt_one)] with n hn
  have habs : |A * (roundedLogRadius C n : ℝ)| ≤ (n : ℝ) ^ ε := by
    simpa only [one_mul, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) ε)] using hn
  exact (le_abs_self _).trans habs

/-- The source radius is eventually below every positive power of the system
size (`08-scanner.tex`, logarithmic-radius choice). -/
theorem eventually_roundedLogRadius_le_rpow {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (roundedLogRadius C n : ℝ) ≤ (n : ℝ) ^ ε := by
  simpa only [one_mul] using eventually_const_mul_roundedLogRadius_le_rpow hC hε 1

/-- Every fixed multiple of the cubed splitting radius is eventually below a
positive power, as used in the bad-history ratio of `08-scanner.tex`. -/
theorem eventually_const_mul_roundedLogRadius_cube_le_rpow {C ε : ℝ}
    (hC : 0 ≤ C) (hε : 0 < ε) (A : ℝ) :
    ∀ᶠ n : ℕ in atTop, A * (roundedLogRadius C n : ℝ) ^ 3 ≤ (n : ℝ) ^ ε := by
  have h := ((isLittleO_roundedLogRadius_rpow hC (div_pos hε (by norm_num :
    (0 : ℝ) < 3))).pow (by norm_num : 0 < (3 : ℕ))).const_mul_left A
  filter_upwards [h.bound (show (0 : ℝ) < 1 from zero_lt_one)] with n hn
  have hp : ((n : ℝ) ^ (ε / 3)) ^ (3 : ℕ) = (n : ℝ) ^ ε := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
    congr 1
    simp
  rw [hp] at hn
  have habs : |A * (roundedLogRadius C n : ℝ) ^ 3| ≤ (n : ℝ) ^ ε := by
    simpa only [one_mul, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) ε)] using hn
  exact (le_abs_self _).trans habs

/-- A positive source constant makes the rounded splitting radius positive for
all sufficiently large system sizes (`08-scanner.tex`, line 49). -/
theorem eventually_one_le_roundedLogRadius {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ roundedLogRadius C n := by
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
  exact Nat.one_le_ceil_iff.mpr
    (mul_pos hC (sq_pos_of_pos (Real.log_pos (by exact_mod_cast hn))))

end TNLean.PEPS.AreaLaw.Scan

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Positivity
import TNLean.Algebra.ExplicitThresholds

/-!
# The rounded logarithmic splitting radius

The splitting radius `⌈C log² n⌉` and every fixed multiple of its cube grow more
slowly than every positive power of `n`. The threshold beyond which
`A ⌈C log² n⌉ ^ j ≤ n ^ ε` is given explicitly by `roundedLogRadiusThreshold`.

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

/-- The explicit threshold beyond which `A ⌈C log² n⌉ ^ j ≤ n ^ ε`: `n ≥ 3`, so that
`log n ≥ 1` and `⌈C log² n⌉ ≤ (C + 1) log² n`, and the logarithmic-power threshold for
`max A 0 (C + 1) ^ j (log n) ^ (2 j) ≤ n ^ ε`. The radius is that of `08-scanner.tex`,
line 49. -/
noncomputable def roundedLogRadiusThreshold (C ε A : ℝ) (j : ℕ) : ℕ :=
  max 3 ⌈Real.logPowThreshold (max A 0 * (C + 1) ^ j) 1 ε (2 * j)⌉₊

/-- For `n ≥ 3`, the rounded radius is at most `(C + 1) log² n`. -/
theorem roundedLogRadius_le_mul_log_sq {C : ℝ} (hC : 0 ≤ C) {n : ℕ} (hn : 3 ≤ n) :
    (roundedLogRadius C n : ℝ) ≤ (C + 1) * Real.log n ^ 2 := by
  have hlog := Real.one_le_log_natCast_of_three_le hn
  have hsq : 1 ≤ Real.log n ^ 2 := one_le_pow₀ hlog
  have hceil := (Nat.ceil_lt_add_one (mul_nonneg hC (sq_nonneg (Real.log n)))).le
  unfold roundedLogRadius
  linarith

/-- A fixed multiple of a power of the source radius is below `n ^ ε` at every `n` from the
explicit threshold `roundedLogRadiusThreshold C ε A j` on (`08-scanner.tex`, line 49, and the
cutoffs of the bad-history estimate). -/
theorem const_mul_roundedLogRadius_pow_le_rpow_of_threshold_le {C ε : ℝ} (hC : 0 ≤ C)
    (hε : 0 < ε) (A : ℝ) (j : ℕ) {n : ℕ} (hthr : roundedLogRadiusThreshold C ε A j ≤ n) :
    A * (roundedLogRadius C n : ℝ) ^ j ≤ (n : ℝ) ^ ε := by
  have hn3 : 3 ≤ n := (le_max_left _ _).trans hthr
  have hA : 0 ≤ max A 0 := le_max_right A 0
  have hr := roundedLogRadius_le_mul_log_sq hC hn3
  have hpow : (roundedLogRadius C n : ℝ) ^ j ≤ ((C + 1) * Real.log n ^ 2) ^ j :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hr j
  have hlog := Real.mul_log_pow_le_mul_rpow_of_ceil_logPowThreshold_le
    (mul_nonneg hA (pow_nonneg (by linarith) j)) one_pos hε ((le_max_right _ _).trans hthr)
  calc A * (roundedLogRadius C n : ℝ) ^ j ≤ max A 0 * (roundedLogRadius C n : ℝ) ^ j :=
        mul_le_mul_of_nonneg_right (le_max_left A 0) (by positivity)
    _ ≤ max A 0 * ((C + 1) * Real.log n ^ 2) ^ j := mul_le_mul_of_nonneg_left hpow hA
    _ = max A 0 * (C + 1) ^ j * Real.log n ^ (2 * j) := by rw [mul_pow, ← pow_mul]; ring
    _ ≤ (n : ℝ) ^ ε := by simpa only [one_mul] using hlog

/-- Every fixed multiple of the source radius is eventually below any positive
power, as required for the cutoffs in `08-scanner.tex`. -/
theorem eventually_const_mul_roundedLogRadius_le_rpow {C ε : ℝ}
    (hC : 0 ≤ C) (hε : 0 < ε) (A : ℝ) :
    ∀ᶠ n : ℕ in atTop, A * (roundedLogRadius C n : ℝ) ≤ (n : ℝ) ^ ε :=
  eventually_atTop.2 ⟨roundedLogRadiusThreshold C ε A 1, fun _ hn => by
    simpa only [pow_one] using const_mul_roundedLogRadius_pow_le_rpow_of_threshold_le hC hε A 1 hn⟩

/-- The source radius is eventually below every positive power of the system
size (`08-scanner.tex`, logarithmic-radius choice). -/
theorem eventually_roundedLogRadius_le_rpow {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (roundedLogRadius C n : ℝ) ≤ (n : ℝ) ^ ε := by
  simpa only [one_mul] using eventually_const_mul_roundedLogRadius_le_rpow hC hε 1

/-- Every fixed multiple of the cubed splitting radius is eventually below a
positive power, as used in the bad-history ratio of `08-scanner.tex`. -/
theorem eventually_const_mul_roundedLogRadius_cube_le_rpow {C ε : ℝ}
    (hC : 0 ≤ C) (hε : 0 < ε) (A : ℝ) :
    ∀ᶠ n : ℕ in atTop, A * (roundedLogRadius C n : ℝ) ^ 3 ≤ (n : ℝ) ^ ε :=
  eventually_atTop.2 ⟨_, fun _ => const_mul_roundedLogRadius_pow_le_rpow_of_threshold_le hC hε A 3⟩

/-- A positive source constant makes the rounded splitting radius positive at every
`n ≥ 2` (`08-scanner.tex`, line 49). -/
theorem one_le_roundedLogRadius_of_two_le {C : ℝ} (hC : 0 < C) {n : ℕ} (hn : 2 ≤ n) :
    1 ≤ roundedLogRadius C n :=
  Nat.one_le_ceil_iff.mpr
    (mul_pos hC (sq_pos_of_pos (Real.log_pos (by exact_mod_cast hn))))

/-- A positive source constant makes the rounded splitting radius positive for
all sufficiently large system sizes (`08-scanner.tex`, line 49). -/
theorem eventually_one_le_roundedLogRadius {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ roundedLogRadius C n :=
  eventually_atTop.2 ⟨2, fun _ => one_le_roundedLogRadius_of_two_le hC⟩

end TNLean.PEPS.AreaLaw.Scan

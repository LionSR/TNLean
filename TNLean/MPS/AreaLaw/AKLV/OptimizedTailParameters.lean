/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.SequenceParameters

/-!
# Accuracy-dependent window and polynomial parameters

The window is enlarged by twice the rounded fourth root of the cube of the
accuracy logarithm divided by the gap. The polynomial degree retains the
source square-root spectral-ceiling dependence.

Source: AKLV, arXiv:1301.1162v1, lines 1503--1517. The exact logarithmic
rank expression is retained; its fourth-root comparison is a separate
estimate from the shrinking and physical approximation statements.
-/

open Real

namespace TNLean.MPS.AreaLaw

/-- Logarithmic accuracy scale for a requested squared error. -/
noncomputable def aklvAccuracyLog (rho : ℝ) : ℝ := log (128 / rho)

/-- Rounded fourth-root increment in the accuracy-dependent window. -/
noncomputable def aklvAccuracyIncrement (g rho : ℝ) : ℕ :=
  ⌈sqrt (sqrt (aklvAccuracyLog rho ^ 3 / g))⌉₊

/-- The enlarged width preserves the parity of the initial physical window. -/
noncomputable def aklvAccuracyWidth (s0 : ℕ) (g rho : ℝ) : ℕ :=
  s0 + 2 * aklvAccuracyIncrement g rho

/-- Threshold making the clipped target accurate at the requested scale. -/
noncomputable def aklvAccuracyThreshold (g rho : ℝ) : ℝ :=
  aklvLogarithmicThreshold g + 16 * aklvAccuracyLog rho

/-- Degree for the actual polynomial at the enlarged width. -/
noncomputable def aklvAccuracyDegree (g rho : ℝ) (s : ℕ) : ℕ :=
  ⌈aklvAccuracyLog rho * sqrt ((2 * aklvAccuracyThreshold g rho + s) / g)⌉₊

/-- Exact common rank budget for the filtered and boundary alternatives. -/
noncomputable def aklvAccuracyRankBound (q s0 : ℕ) (g rho : ℝ) : ℕ :=
  let s := aklvAccuracyWidth s0 g rho
  let ell := aklvAccuracyDegree g rho s
  max ((q * (s0 ^ 2 + 1)) ^ (32 * (2 * s0 + 1)) *
    (q * (ell + 1)) ^ (32 * (ell / s + Nat.sqrt ell + 1))) (q ^ (s - s / 2))

/-- The logarithmic scale is at least one and its negative exponential is
exactly the requested squared error divided by 128. -/
theorem aklvAccuracyLog_bounds {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    1 ≤ aklvAccuracyLog rho ∧ exp (-aklvAccuracyLog rho) = rho / 128 := by
  have hlog2 : (1 : ℝ) / 2 ≤ log 2 := by
    have h := one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have h128 : (1 : ℝ) ≤ log 128 := by
    have hid : log (128 : ℝ) = 7 * log 2 := by
      rw [show (128 : ℝ) = 2 ^ 7 by norm_num, log_pow]
      norm_num
    rw [hid]
    linarith
  constructor
  · apply h128.trans
    apply log_le_log (by norm_num)
    exact (le_div_iff₀ hrho).mpr (by nlinarith)
  · rw [aklvAccuracyLog, exp_neg, exp_log (by positivity)]
    field_simp

/-- The accuracy threshold is above the physical threshold and positive. -/
theorem aklvAccuracyThreshold_bounds {g rho : ℝ}
    (hg : 0 < g) (hg1 : g ≤ 1) (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    aklvLogarithmicThreshold g ≤ aklvAccuracyThreshold g rho ∧
      0 < aklvAccuracyThreshold g rho ∧
      exp (-aklvAccuracyThreshold g rho / 16) ≤ rho / 128 := by
  have hz := (aklvAccuracyLog_bounds hrho hrho1).1
  have hT : 0 ≤ aklvLogarithmicThreshold g := by
    have hlog := log_nonneg ((one_le_div hg).mpr hg1)
    unfold aklvLogarithmicThreshold
    positivity
  have ht : aklvLogarithmicThreshold g ≤ aklvAccuracyThreshold g rho := by
    unfold aklvAccuracyThreshold
    linarith
  refine ⟨ht, by unfold aklvAccuracyThreshold; linarith, ?_⟩
  have hid : -aklvAccuracyThreshold g rho / 16 =
      -aklvLogarithmicThreshold g / 16 - aklvAccuracyLog rho := by
    unfold aklvAccuracyThreshold
    ring
  rw [hid, exp_sub, div_eq_mul_inv, ← exp_neg,
    (aklvAccuracyLog_bounds hrho hrho1).2]
  have hexp : exp (-aklvLogarithmicThreshold g / 16) ≤ 1 :=
    exp_le_one_iff.mpr (by linarith)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hexp (by positivity : 0 ≤ rho / 128)

/-- The selected actual degree makes the squared shrinking factor quadratic
in the requested squared error. -/
theorem aklvAccuracyDegree_shrink_le {g rho : ℝ} (hg : 0 < g) (hg1 : g ≤ 1)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (s : ℕ) :
    (2 * exp (-2 * (aklvAccuracyDegree g rho s : ℝ) *
      sqrt ((9 * g / 10) / (2 * aklvAccuracyThreshold g rho + s)))) ^ 2 ≤
        rho ^ 2 / 4096 := by
  let z := aklvAccuracyLog rho
  let W := 2 * aklvAccuracyThreshold g rho + s
  let ell := aklvAccuracyDegree g rho s
  have hz : 0 ≤ z := by linarith [(aklvAccuracyLog_bounds hrho hrho1).1]
  have hW : 0 < W := by
    have ht := (aklvAccuracyThreshold_bounds hg hg1 hrho hrho1).2.1
    dsimp only [W]
    positivity
  have hproduct : sqrt (W / g) * sqrt ((9 * g / 10) / W) = sqrt (9 / 10) := by
    rw [← sqrt_mul (div_nonneg hW.le hg.le)]
    congr 1
    field_simp
  have hroot : (1 : ℝ) / 2 ≤ sqrt (9 / 10) := le_sqrt_of_sq_le (by norm_num)
  have hdegree : z * sqrt (W / g) ≤ (ell : ℝ) := Nat.le_ceil _
  have hscaled : 2 * z ≤ 4 * (ell : ℝ) * sqrt ((9 * g / 10) / W) := by
    have hmul := mul_le_mul_of_nonneg_right hdegree (sqrt_nonneg ((9 * g / 10) / W))
    have hzroot := mul_le_mul_of_nonneg_left hroot hz
    nlinarith [hproduct]
  have hexp : exp (-(2 * z)) = rho ^ 2 / 16384 := by
    have heq : -(2 * z) = (2 : ℕ) * (-z) := by push_cast; ring
    rw [heq, exp_nat_mul, (aklvAccuracyLog_bounds hrho hrho1).2]
    ring
  change (2 * exp (-2 * (ell : ℝ) * sqrt ((9 * g / 10) / W))) ^ 2 ≤ _
  calc
    _ = 4 * exp (-(4 * (ell : ℝ) * sqrt ((9 * g / 10) / W))) := by
      rw [mul_pow, ← exp_nat_mul]
      congr 2 <;> norm_num
      ring
    _ ≤ 4 * exp (-(2 * z)) := by
      apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith)) (by norm_num)
    _ = rho ^ 2 / 4096 := by rw [hexp]; ring

/-- The physical refinement's two actual error terms fit within the request. -/
theorem aklvAccuracy_refinement_error_le {g rho : ℝ} (hg : 0 < g) (hg1 : g ≤ 1)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (s : ℕ) :
    16 * (2 * exp (-2 * (aklvAccuracyDegree g rho s : ℝ) *
      sqrt ((9 * g / 10) / (2 * aklvAccuracyThreshold g rho + s)))) ^ 2 +
      exp (-aklvAccuracyThreshold g rho / 16) / 50 ≤ rho := by
  have hdelta := aklvAccuracyDegree_shrink_le hg hg1 hrho hrho1 s
  have htarget := (aklvAccuracyThreshold_bounds hg hg1 hrho hrho1).2.2
  have hsquare : rho ^ 2 ≤ rho := by nlinarith
  nlinarith

/-- The integer increment retains the exact fourth-root scale. -/
theorem aklvAccuracyIncrement_bounds (g rho : ℝ) :
    sqrt (sqrt (aklvAccuracyLog rho ^ 3 / g)) ≤
        (aklvAccuracyIncrement g rho : ℝ) ∧
      (aklvAccuracyIncrement g rho : ℝ) <
        sqrt (sqrt (aklvAccuracyLog rho ^ 3 / g)) + 1 := by
  exact ⟨Nat.le_ceil _, Nat.ceil_lt_add_one (sqrt_nonneg _)⟩

/-- The common rank budget retains exactly the sharp logarithmic expression
and the exact boundary cost. No exponential-in-degree estimate is substituted. -/
theorem aklvAccuracyRankBound_log {q : ℕ} (hq : 1 ≤ q) (s0 : ℕ) (g rho : ℝ) :
    let s := aklvAccuracyWidth s0 g rho
    let ell := aklvAccuracyDegree g rho s
    let D0 : ℕ := (q * (s0 ^ 2 + 1)) ^ (32 * (2 * s0 + 1))
    log (aklvAccuracyRankBound q s0 g rho : ℝ) =
      max (log (D0 : ℝ) + ((32 * (ell / s + Nat.sqrt ell + 1) : ℕ) : ℝ) *
        log ((q * (ell + 1) : ℕ) : ℝ))
        (((s - s / 2 : ℕ) : ℝ) * log (q : ℝ)) := by
  intro s ell D0
  let D : ℕ := (q * (ell + 1)) ^ (32 * (ell / s + Nat.sqrt ell + 1))
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hD0 : 0 < (D0 : ℝ) := by dsimp only [D0]; positivity
  have hD : 0 < (D : ℝ) := by dsimp only [D]; positivity
  have hlog : log ((D0 * D : ℕ) : ℝ) =
      log (D0 : ℝ) + ((32 * (ell / s + Nat.sqrt ell + 1) : ℕ) : ℝ) *
        log ((q * (ell + 1) : ℕ) : ℝ) := by
    rw [Nat.cast_mul, log_mul (ne_of_gt hD0) (ne_of_gt hD)]
    simp only [D, Nat.cast_pow, log_pow]
  have hboundary : log ((q ^ (s - s / 2) : ℕ) : ℝ) =
      (((s - s / 2 : ℕ) : ℝ) * log (q : ℝ)) := by
    rw [Nat.cast_pow, log_pow]
  change log ((max (D0 * D) (q ^ (s - s / 2)) : ℕ) : ℝ) = _
  rcases le_total (D0 * D) (q ^ (s - s / 2)) with hle | hle
  · have hlogle : log ((D0 * D : ℕ) : ℝ) ≤ log ((q ^ (s - s / 2) : ℕ) : ℝ) :=
      log_le_log (by rw [Nat.cast_mul]; exact mul_pos hD0 hD) (by exact_mod_cast hle)
    rw [hlog, hboundary] at hlogle
    rw [max_eq_right hle, hboundary, max_eq_right hlogle]
  · have hlogle : log ((q ^ (s - s / 2) : ℕ) : ℝ) ≤ log ((D0 * D : ℕ) : ℝ) :=
      log_le_log (by rw [Nat.cast_pow]; exact pow_pos hqpos _) (by exact_mod_cast hle)
    rw [hboundary, hlog] at hlogle
    rw [max_eq_left hle, hlog, max_eq_left hlogle]

end TNLean.MPS.AreaLaw

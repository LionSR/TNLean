/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.OptimizedTailParameters

/-!
# Degree bounds for the fourth-root accuracy scale

The actual square-root degree from the accuracy-window construction is
bounded quadratically either by the initial width or by the fourth-root
increment, according to the larger scale. These scalar estimates retain
the actual selected polynomial parameters.

Source: AKLV, arXiv:1301.1162v1, lines 1503--1517.
-/

open Real

namespace TNLean.MPS.AreaLaw

/-- Above any width dominating the inverse gap, the increment is less
than the accuracy logarithm plus one. -/
theorem aklvAccuracyIncrement_lt_log_add_one {g rho : ℝ}
    (s0 : ℕ) (hgap : 1 / g ≤ (s0 : ℝ))
    (hscale : (s0 : ℝ) ≤ aklvAccuracyLog rho) :
    (aklvAccuracyIncrement g rho : ℝ) < aklvAccuracyLog rho + 1 := by
  let z := aklvAccuracyLog rho
  let r := sqrt (sqrt (z ^ 3 / g))
  have hz : 0 ≤ z := (Nat.cast_nonneg s0).trans hscale
  have harg : z ^ 3 / g ≤ z ^ 4 := by
    calc
      _ = z ^ 3 * (1 / g) := by ring
      _ ≤ z ^ 3 * z := mul_le_mul_of_nonneg_left (hgap.trans hscale) (pow_nonneg hz 3)
      _ = _ := by ring
  have hrz : r ≤ z := by
    calc
      _ ≤ sqrt (sqrt (z ^ 4)) := sqrt_le_sqrt (sqrt_le_sqrt harg)
      _ = z := by
        rw [show z ^ 4 = (z ^ 2) ^ 2 by ring, sqrt_sq (sq_nonneg z), sqrt_sq hz]
  have hm : (aklvAccuracyIncrement g rho : ℝ) < r + 1 :=
    (aklvAccuracyIncrement_bounds g rho).2
  linarith

/-- At logarithmic accuracy above the initial-width scale, the actual
selected degree is quadratic in the fourth-root increment. The auxiliary
initial-width bounds are derived from the uniform physical width later. -/
theorem aklvAccuracyDegree_le_large_square {g rho : ℝ}
    (hg : 0 < g) (hg1 : g ≤ 1) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (s0 : ℕ) (hgap : 1 / g ≤ (s0 : ℝ))
    (hT : aklvLogarithmicThreshold g ≤ 1040 * (s0 : ℝ))
    (hscale : (s0 : ℝ) ≤ aklvAccuracyLog rho) :
    aklvAccuracyDegree g rho (aklvAccuracyWidth s0 g rho) ≤
      66 * aklvAccuracyIncrement g rho ^ 2 := by
  let z := aklvAccuracyLog rho
  let r := sqrt (sqrt (z ^ 3 / g))
  let m := aklvAccuracyIncrement g rho
  let W := 2 * aklvAccuracyThreshold g rho + aklvAccuracyWidth s0 g rho
  have hz1 : 1 ≤ z := (aklvAccuracyLog_bounds hrho hrho1).1
  have hz : 0 ≤ z := by linarith
  have hm : (m : ℝ) < z + 1 :=
    aklvAccuracyIncrement_lt_log_add_one s0 hgap hscale
  have hW : W ≤ 4225 * z := by
    dsimp only [W, aklvAccuracyThreshold, aklvAccuracyWidth]
    push_cast
    change aklvLogarithmicThreshold g ≤ 1040 * (s0 : ℝ) at hT
    nlinarith
  have hWpos : 0 < W := by
    have ht := (aklvAccuracyThreshold_bounds hg hg1 hrho hrho1).2.1
    dsimp only [W]
    positivity
  have hr4 : r ^ 4 = z ^ 3 / g := by
    dsimp only [r]
    rw [show sqrt (sqrt (z ^ 3 / g)) ^ 4 =
      (sqrt (sqrt (z ^ 3 / g)) ^ 2) ^ 2 by ring,
      sq_sqrt (sqrt_nonneg _), sq_sqrt (div_nonneg (pow_nonneg hz 3) hg.le)]
  have hpower : z ^ 3 / g ≤ (m : ℝ) ^ 4 := by
    have h := pow_le_pow_left₀ (sqrt_nonneg (sqrt (z ^ 3 / g)))
      (aklvAccuracyIncrement_bounds g rho).1 4
    rwa [hr4] at h
  have hdegree : z * sqrt (W / g) ≤ 65 * (m : ℝ) ^ 2 := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, sq_sqrt (div_nonneg hWpos.le hg.le)]
    have hmul := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hW hg.le) (sq_nonneg z)
    calc
      z ^ 2 * (W / g) ≤ 4225 * (z ^ 3 / g) := by
        convert hmul using 1
        ring
      _ ≤ 4225 * (m : ℝ) ^ 4 := mul_le_mul_of_nonneg_left hpower (by norm_num)
      _ = (65 * (m : ℝ) ^ 2) ^ 2 := by ring
  apply Nat.ceil_le.mpr
  push_cast
  change z * sqrt (W / g) ≤ 66 * (m : ℝ) ^ 2
  nlinarith [sq_nonneg (m : ℝ)]

/-- Below the initial-width logarithmic scale, the selected degree is
quadratic in that initial width. -/
theorem aklvAccuracyDegree_le_initial_square {g rho : ℝ}
    (hg : 0 < g) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (s0 : ℕ) (hgap : 1 / g ≤ (s0 : ℝ))
    (hT : aklvLogarithmicThreshold g ≤ 1040 * (s0 : ℝ))
    (hscale : aklvAccuracyLog rho ≤ (s0 : ℝ)) :
    aklvAccuracyDegree g rho (aklvAccuracyWidth s0 g rho) ≤ 66 * s0 ^ 2 := by
  let z := aklvAccuracyLog rho
  let r := sqrt (sqrt (z ^ 3 / g))
  let m := aklvAccuracyIncrement g rho
  let W := 2 * aklvAccuracyThreshold g rho + aklvAccuracyWidth s0 g rho
  have hz : 0 ≤ z := by linarith [(aklvAccuracyLog_bounds hrho hrho1).1]
  have harg : z ^ 3 / g ≤ (s0 : ℝ) ^ 4 := by
    calc
      _ = z ^ 3 * (1 / g) := by ring
      _ ≤ (s0 : ℝ) ^ 3 * (s0 : ℝ) :=
        mul_le_mul (pow_le_pow_left₀ hz hscale 3) hgap (by positivity) (by positivity)
      _ = _ := by ring
  have hr : r ≤ (s0 : ℝ) := by
    calc
      _ ≤ sqrt (sqrt ((s0 : ℝ) ^ 4)) := sqrt_le_sqrt (sqrt_le_sqrt harg)
      _ = (s0 : ℝ) := by
        rw [show (s0 : ℝ) ^ 4 = ((s0 : ℝ) ^ 2) ^ 2 by ring,
          sqrt_sq (sq_nonneg _), sqrt_sq (Nat.cast_nonneg _)]
  have hm : m ≤ s0 := Nat.ceil_le.mpr hr
  have hW : W ≤ 4225 * (s0 : ℝ) := by
    dsimp only [W, aklvAccuracyThreshold, aklvAccuracyWidth]
    push_cast
    have hmR : (m : ℝ) ≤ s0 := by exact_mod_cast hm
    nlinarith
  have hWG : W / g ≤ 4225 * (s0 : ℝ) ^ 2 := by
    calc
      _ ≤ (4225 * (s0 : ℝ)) / g := div_le_div_of_nonneg_right hW hg.le
      _ = 4225 * (s0 : ℝ) * (1 / g) := by ring
      _ ≤ 4225 * (s0 : ℝ) * (s0 : ℝ) :=
        mul_le_mul_of_nonneg_left hgap (by positivity)
      _ = _ := by ring
  have hroot : sqrt (W / g) ≤ 65 * (s0 : ℝ) := by
    calc
      _ ≤ sqrt ((65 * (s0 : ℝ)) ^ 2) := sqrt_le_sqrt (by nlinarith only [hWG])
      _ = _ := sqrt_sq (by positivity)
  have hdegree := mul_le_mul hscale hroot (sqrt_nonneg (W / g)) (Nat.cast_nonneg s0)
  apply Nat.ceil_le.mpr
  push_cast
  change z * sqrt (W / g) ≤ 66 * (s0 : ℝ) ^ 2
  nlinarith [sq_nonneg (s0 : ℝ)]

/-- The fourth-root increment is nonzero for the requested accuracy scales. -/
theorem aklvAccuracyIncrement_pos {g rho : ℝ} (hg : 0 < g) (hg1 : g ≤ 1)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) : 1 ≤ aklvAccuracyIncrement g rho := by
  have hz : 1 ≤ aklvAccuracyLog rho := (aklvAccuracyLog_bounds hrho hrho1).1
  have harg : 1 ≤ aklvAccuracyLog rho ^ 3 / g :=
    (one_le_div hg).mpr (hg1.trans (one_le_pow₀ hz))
  have hr : 1 ≤ sqrt (sqrt (aklvAccuracyLog rho ^ 3 / g)) := by
    exact one_le_sqrt.mpr (one_le_sqrt.mpr harg)
  exact_mod_cast hr.trans (aklvAccuracyIncrement_bounds g rho).1

end TNLean.MPS.AreaLaw

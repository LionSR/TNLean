/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.OptimizedInitialScale

/-!
# The uniform fourth-root logarithmic rank comparison

The maximum of the actual filtered rank and the exact boundary rank is
controlled by the initial logarithmic cost and the fourth-root accuracy
scale. The selected operators and degrees remain those of `AccuracyWindow`.

Source: AKLV, arXiv:1301.1162v1, lines 1503--1517.
-/

open Real

namespace TNLean.MPS.AreaLaw

/-- The original-site contribution to the boundary rank is absorbed in the
actual initial logarithmic rank budget. -/
private theorem aklv_width_log_le_initial_rank {q s0 : ℕ} (hq : 1 ≤ q) :
    (s0 : ℝ) * log (q : ℝ) ≤
      log (((q * (s0 ^ 2 + 1)) ^ (32 * (2 * s0 + 1)) : ℕ) : ℝ) := by
  let b := q * (s0 ^ 2 + 1)
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hqb : q ≤ b := by dsimp only [b]; nlinarith
  have hbase := log_le_log hqpos (show (q : ℝ) ≤ (b : ℝ) by exact_mod_cast hqb)
  have hbase0 : 0 ≤ log (b : ℝ) := log_natCast_nonneg b
  have hmul := mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg s0)
  rw [Nat.cast_pow, log_pow]
  change (s0 : ℝ) * log (q : ℝ) ≤ ((32 * (2 * s0 + 1) : ℕ) : ℝ) * log (b : ℝ)
  push_cast
  nlinarith [mul_nonneg (Nat.cast_nonneg s0) hbase0]

/-- The two scale regimes control the exact maximum of the filtered and
boundary logarithmic ranks. All auxiliary initial-width bounds are scalar. -/
theorem aklvAccuracyRankBound_log_le_cost {q : ℕ} (hq : 2 ≤ q)
    {g rho : ℝ} (hg : 0 < g) (hg1 : g ≤ 1) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (s0 : ℕ) (hs0 : 1 ≤ s0) (hgap : 1 / g ≤ (s0 : ℝ))
    (hT : aklvLogarithmicThreshold g ≤ 1040 * (s0 : ℝ)) :
    let z := aklvAccuracyLog rho
    let m := aklvAccuracyIncrement g rho
    let D0 : ℕ := (q * (s0 ^ 2 + 1)) ^ (32 * (2 * s0 + 1))
    log (aklvAccuracyRankBound q s0 g rho : ℝ) ≤
      10001 * log (D0 : ℝ) + 400000 * (m : ℝ) * (1 + log (q : ℝ) + log (z + 1)) := by
  intro z m D0
  let s := aklvAccuracyWidth s0 g rho
  let ell := aklvAccuracyDegree g rho s
  let D : ℕ := (q * (ell + 1)) ^ (32 * (ell / s + Nat.sqrt ell + 1))
  let V := 1 + log (q : ℝ) + log (z + 1)
  have hz : 1 ≤ z := (aklvAccuracyLog_bounds hrho hrho1).1
  have hqlog : 0 ≤ log (q : ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
  have hZlog : 0 ≤ log (z + 1) := log_nonneg (by linarith)
  have hV : 0 ≤ V := by dsimp only [V]; linarith
  have hD0 : 0 ≤ log (D0 : ℝ) := log_natCast_nonneg D0
  have hfilter : log (D : ℝ) ≤ 10000 * log (D0 : ℝ) + 400000 * (m : ℝ) * V := by
    rcases le_total z (s0 : ℝ) with hscale | hscale
    · have hell := aklvAccuracyDegree_le_initial_square hg hrho hrho1 s0 hgap hT hscale
      have hcost := aklv_log_rank_le_initial_cost hq hs0
        (show s0 ≤ s from Nat.le_add_right _ _) hell
      have hnonneg := mul_nonneg (Nat.cast_nonneg m) hV
      change log (D : ℝ) ≤ 10000 * log (D0 : ℝ) at hcost
      nlinarith
    · have hm : 1 ≤ m := aklvAccuracyIncrement_pos hg hg1 hrho hrho1
      have hms : m ≤ s := by change m ≤ s0 + 2 * m; omega
      have hell := aklvAccuracyDegree_le_large_square hg hg1 hrho hrho1 s0 hgap hT hscale
      have hmz : (m : ℝ) ≤ z + 1 :=
        (aklvAccuracyIncrement_lt_log_add_one s0 hgap hscale).le
      have hcost := aklv_log_rank_le_accuracy_cost hq hm hms hell hz hmz
      change log (D : ℝ) ≤ 400000 * (m : ℝ) * V at hcost
      linarith
  have hboundary : (((s - s / 2 : ℕ) : ℝ) * log (q : ℝ)) ≤
      log (D0 : ℝ) + 2 * (m : ℝ) * V := by
    have hwidth := aklv_width_log_le_initial_rank (s0 := s0) (by omega : 1 ≤ q)
    change (s0 : ℝ) * log (q : ℝ) ≤ log (D0 : ℝ) at hwidth
    have hS : ((s - s / 2 : ℕ) : ℝ) ≤ s := by exact_mod_cast Nat.sub_le s (s / 2)
    have hfirst := mul_le_mul_of_nonneg_right hS hqlog
    have hqV : log (q : ℝ) ≤ V := by dsimp only [V]; linarith
    have hsecond := mul_le_mul_of_nonneg_left hqV (show 0 ≤ 2 * (m : ℝ) by positivity)
    dsimp only [s, aklvAccuracyWidth] at hfirst
    push_cast at hfirst
    change (((s - s / 2 : ℕ) : ℝ) * log (q : ℝ)) ≤
      ((s0 : ℝ) + 2 * (m : ℝ)) * log (q : ℝ) at hfirst
    nlinarith
  have hlogD : log (D : ℝ) = ((32 * (ell / s + Nat.sqrt ell + 1) : ℕ) : ℝ) *
      log ((q * (ell + 1) : ℕ) : ℝ) := by
    dsimp only [D]
    rw [Nat.cast_pow, log_pow]
  have hlogB := aklvAccuracyRankBound_log (by omega : 1 ≤ q) s0 g rho
  change log (aklvAccuracyRankBound q s0 g rho : ℝ) =
    max (log (D0 : ℝ) + _) _ at hlogB
  rw [← hlogD] at hlogB
  rw [hlogB]
  apply max_le
  · nlinarith only [hfilter, hD0]
  · nlinarith [mul_nonneg (Nat.cast_nonneg m) hV]

/-- A universal coefficient for the complete fourth-root logarithmic bound. -/
noncomputable def aklvAccuracyLogCoefficient (A : ℝ) : ℝ :=
  10001 * aklvInitialRankLogCoefficient A + 800000

/-- The exact selected rank budget has the source's fourth-root accuracy
scale, with its gap and logarithmic dependence explicit. -/
theorem aklvAccuracyRankBound_log_le_fourthRoot {A g rho : ℝ}
    (hA : 1 ≤ A) (hg : 0 < g) (hg1 : g ≤ 1) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (q : ℕ) (hq : 2 ≤ q) :
    let u := 1 + log (q : ℝ) + log (1 / g)
    let z := aklvAccuracyLog rho
    let s0 : ℕ := ⌈A * u ^ 2 / g⌉₊
    log (aklvAccuracyRankBound q s0 g rho : ℝ) ≤
      aklvAccuracyLogCoefficient A *
        (u ^ 3 / g + sqrt (sqrt (z ^ 3 / g)) * (u + log (z + 1))) := by
  intro u z s0
  obtain ⟨hu, hs0, hgap, _hloggap, hT, _hupper, hinit⟩ :=
    aklv_initial_width_bounds hA hg hg1 q (by omega)
  have hcost := aklvAccuracyRankBound_log_le_cost hq hg hg1 hrho hrho1 s0 hs0 hgap hT
  let D0 : ℕ := (q * (s0 ^ 2 + 1)) ^ (32 * (2 * s0 + 1))
  change log (D0 : ℝ) ≤ aklvInitialRankLogCoefficient A / g * u ^ 3 at hinit
  let r := sqrt (sqrt (z ^ 3 / g))
  let m := aklvAccuracyIncrement g rho
  let V := 1 + log (q : ℝ) + log (z + 1)
  have hz : 1 ≤ z := (aklvAccuracyLog_bounds hrho hrho1).1
  have hr : 1 ≤ r := by
    exact one_le_sqrt.mpr (one_le_sqrt.mpr ((one_le_div hg).mpr (hg1.trans (one_le_pow₀ hz))))
  have hm : (m : ℝ) ≤ 2 * r := by
    have h := (aklvAccuracyIncrement_bounds g rho).2
    change (m : ℝ) < r + 1 at h
    linarith
  have hglog : 0 ≤ log (1 / g) := log_nonneg ((one_le_div hg).mpr hg1)
  have hqlog : 0 ≤ log (q : ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
  have hZlog : 0 ≤ log (z + 1) := log_nonneg (by linarith)
  have hV : 0 ≤ V := by dsimp only [V]; linarith
  have hVu : V ≤ u + log (z + 1) := by dsimp only [V, u]; linarith
  have haccuracy := mul_le_mul hm hVu hV (show 0 ≤ 2 * r by linarith)
  have hinit0 : 0 ≤ aklvInitialRankLogCoefficient A := by
    have hlog : 0 ≤ log (A + 1) := log_nonneg (by linarith)
    unfold aklvInitialRankLogCoefficient
    positivity
  have hX : 0 ≤ u ^ 3 / g := by positivity
  have hY : 0 ≤ r * (u + log (z + 1)) := by positivity
  unfold aklvAccuracyLogCoefficient
  change _ ≤ (10001 * aklvInitialRankLogCoefficient A + 800000) *
    (u ^ 3 / g + r * (u + log (z + 1)))
  have hinit' := mul_le_mul_of_nonneg_left hinit (by norm_num : (0 : ℝ) ≤ 10001)
  have haccuracy' := mul_le_mul_of_nonneg_left haccuracy (by norm_num : (0 : ℝ) ≤ 400000)
  have hsum : log (aklvAccuracyRankBound q s0 g rho : ℝ) ≤
      10001 * aklvInitialRankLogCoefficient A * (u ^ 3 / g) +
        800000 * (r * (u + log (z + 1))) := by
    calc
      _ ≤ 10001 * log (D0 : ℝ) + 400000 * (m : ℝ) * V := hcost
      _ ≤ 10001 * (aklvInitialRankLogCoefficient A / g * u ^ 3) +
          400000 * (2 * r * (u + log (z + 1))) := by
        nlinarith only [hinit', haccuracy']
      _ = _ := by ring
  nlinarith [mul_nonneg (show 0 ≤ 10001 * aklvInitialRankLogCoefficient A by positivity) hY]

end TNLean.MPS.AreaLaw

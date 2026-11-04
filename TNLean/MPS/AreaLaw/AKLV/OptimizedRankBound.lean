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

/-- The fourth-root rank estimate with the local-dimension and gap logarithms
kept separate. Compared with `aklvAccuracyRankBound_log_le_fourthRoot`, the
gap logarithm occurs only linearly in the initial contribution. This concerns
the selected numerical rank budget; it does not construct a physical AGSP at
the smaller initial width. -/
theorem aklvAccuracyRankBound_log_le_fourthRoot_separated {A g rho : ℝ}
    (hA : 1 ≤ A) (hg : 0 < g) (hg1 : g ≤ 1) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (q : ℕ) (hq : 2 ≤ q) :
    let v := 1 + log (q : ℝ)
    let w := log (1 / g)
    let z := aklvAccuracyLog rho
    let s0 : ℕ := ⌈A * v ^ 2 / g⌉₊
    log (aklvAccuracyRankBound q s0 g rho : ℝ) ≤
      aklvAccuracyLogCoefficient A *
        ((v ^ 3 + v ^ 2 * w) / g +
          sqrt (sqrt (z ^ 3 / g)) * (v + log (z + 1))) := by
  intro v w z s0
  obtain ⟨hv, hw, hs0, hgap, hT, _hupper, hinit⟩ :=
    aklv_initial_width_separated_bounds hA hg hg1 q (by omega)
  have hcost := aklvAccuracyRankBound_log_le_cost hq hg hg1 hrho hrho1 s0 hs0 hgap hT
  let D0 : ℕ := (q * (s0 ^ 2 + 1)) ^ (32 * (2 * s0 + 1))
  change log (D0 : ℝ) ≤ aklvInitialRankLogCoefficient A / g *
    (v ^ 3 + v ^ 2 * w) at hinit
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
  have hqlog : 0 ≤ log (q : ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
  have hZlog : 0 ≤ log (z + 1) := log_nonneg (by linarith)
  have hV : 0 ≤ V := by dsimp only [V]; linarith
  have hVv : V = v + log (z + 1) := by dsimp only [V, v]
  have haccuracy := mul_le_mul hm hVv.le hV (show 0 ≤ 2 * r by linarith)
  have hinit0 : 0 ≤ aklvInitialRankLogCoefficient A := by
    have hlog : 0 ≤ log (A + 1) := log_nonneg (by linarith)
    unfold aklvInitialRankLogCoefficient
    positivity
  have hX : 0 ≤ (v ^ 3 + v ^ 2 * w) / g := by positivity
  have hY : 0 ≤ r * (v + log (z + 1)) := by positivity
  unfold aklvAccuracyLogCoefficient
  change _ ≤ (10001 * aklvInitialRankLogCoefficient A + 800000) *
    ((v ^ 3 + v ^ 2 * w) / g + r * (v + log (z + 1)))
  have hinit' := mul_le_mul_of_nonneg_left hinit (by norm_num : (0 : ℝ) ≤ 10001)
  have haccuracy' := mul_le_mul_of_nonneg_left haccuracy (by norm_num : (0 : ℝ) ≤ 400000)
  have hsum : log (aklvAccuracyRankBound q s0 g rho : ℝ) ≤
      10001 * aklvInitialRankLogCoefficient A * ((v ^ 3 + v ^ 2 * w) / g) +
        800000 * (r * (v + log (z + 1))) := by
    calc
      _ ≤ 10001 * log (D0 : ℝ) + 400000 * (m : ℝ) * V := hcost
      _ ≤ 10001 * (aklvInitialRankLogCoefficient A / g *
            (v ^ 3 + v ^ 2 * w)) +
          400000 * (2 * r * (v + log (z + 1))) := by
        nlinarith only [hinit', haccuracy']
      _ = _ := by ring
  nlinarith [mul_nonneg (show 0 ≤ 10001 * aklvInitialRankLogCoefficient A by positivity) hY]

/-- The fourth-root accuracy contribution is at most linear in the logarithmic
accuracy scale. This is the scalar comparison used to pass from the sharp AKLV
rank estimate to the logarithmic-accuracy form quoted by LVV. -/
theorem aklv_fourthRoot_accuracy_cost_le_linear {u g z : ℝ}
    (hu : 0 ≤ u) (hg : 0 < g) (hz : 1 ≤ z) :
    sqrt (sqrt (z ^ 3 / g)) * (u + log (z + 1)) ≤
      sqrt (sqrt (2 / g)) * (u + 4) * z := by
  let r := sqrt (sqrt (z ^ 3 / g))
  let w := sqrt (sqrt (z + 1))
  let c := sqrt (sqrt (2 / g))
  have hz0 : 0 ≤ z := by linarith
  have hr0 : 0 ≤ r := sqrt_nonneg _
  have hw0 : 0 ≤ w := sqrt_nonneg _
  have hc0 : 0 ≤ c := sqrt_nonneg _
  have fourthRoot_pow_four (x : ℝ) (hx : 0 ≤ x) : sqrt (sqrt x) ^ 4 = x := by
    rw [show sqrt (sqrt x) ^ 4 = (sqrt (sqrt x) ^ 2) ^ 2 by ring,
      sq_sqrt (sqrt_nonneg x), sq_sqrt hx]
  have hr4 : r ^ 4 = z ^ 3 / g := fourthRoot_pow_four _ (div_nonneg (by positivity) hg.le)
  have hw4 : w ^ 4 = z + 1 := fourthRoot_pow_four _ (by linarith)
  have hc4 : c ^ 4 = 2 / g := fourthRoot_pow_four _ (by positivity)
  have hr_le : r ≤ c * z := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) (mul_nonneg hc0 hz0)
    rw [hr4, mul_pow, hc4]
    rw [show 2 / g * z ^ 4 = (2 * z ^ 4) / g by field_simp]
    apply (div_le_div_iff_of_pos_right hg).2
    nlinarith [sq_nonneg z, mul_nonneg (sq_nonneg z) hz0]
  have hrw_le : r * w ≤ c * z := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) (mul_nonneg hc0 hz0)
    rw [mul_pow, hr4, hw4, mul_pow, hc4]
    rw [show z ^ 3 / g * (z + 1) = (z ^ 3 * (z + 1)) / g by field_simp,
      show 2 / g * z ^ 4 = (2 * z ^ 4) / g by field_simp]
    apply (div_le_div_iff_of_pos_right hg).2
    nlinarith [sq_nonneg z, mul_nonneg (sq_nonneg z) hz0]
  have hlog : log (z + 1) ≤ 4 * w := by
    have h := log_le_rpow_div (show 0 ≤ z + 1 by linarith)
      (show (0 : ℝ) < 1 / 4 by norm_num)
    have hw : (z + 1) ^ (1 / 4 : ℝ) = w := by
      dsimp only [w]
      rw [sqrt_eq_rpow, sqrt_eq_rpow, ← rpow_mul (by linarith : 0 ≤ z + 1)]
      norm_num
    rw [hw] at h
    convert h using 1
    ring
  dsimp only [r, w, c] at hr_le hrw_le ⊢
  have hru := mul_le_mul_of_nonneg_right hr_le hu
  have hrlog := mul_le_mul_of_nonneg_left hlog hr0
  nlinarith

/-- The selected AKLV rank budget has an exponent linear in the logarithmic
accuracy scale. The coefficient is explicit in the local dimension and gap
parameters and independent of the requested accuracy. -/
theorem aklvAccuracyRankBound_log_le_linear {A g rho : ℝ}
    (hA : 1 ≤ A) (hg : 0 < g) (hg1 : g ≤ 1) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (q : ℕ) (hq : 2 ≤ q) :
    let u := 1 + log (q : ℝ) + log (1 / g)
    let z := aklvAccuracyLog rho
    let s0 : ℕ := ⌈A * u ^ 2 / g⌉₊
    log (aklvAccuracyRankBound q s0 g rho : ℝ) ≤
      aklvAccuracyLogCoefficient A *
        (u ^ 3 / g + sqrt (sqrt (2 / g)) * (u + 4) * z) := by
  intro u z s0
  have hu : 0 ≤ u := by
    have hqlog : 0 ≤ log (q : ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
    have hglog : 0 ≤ log (1 / g) := log_nonneg ((one_le_div hg).mpr hg1)
    dsimp only [u]
    linarith
  have hz : 1 ≤ z := (aklvAccuracyLog_bounds hrho hrho1).1
  have hfourth := aklvAccuracyRankBound_log_le_fourthRoot
    hA hg hg1 hrho hrho1 q hq
  change log (aklvAccuracyRankBound q s0 g rho : ℝ) ≤
    aklvAccuracyLogCoefficient A *
      (u ^ 3 / g + sqrt (sqrt (z ^ 3 / g)) * (u + log (z + 1))) at hfourth
  have hlinear := aklv_fourthRoot_accuracy_cost_le_linear hu hg hz
  have hC : 0 ≤ aklvAccuracyLogCoefficient A := by
    have hlog : 0 ≤ log (A + 1) := log_nonneg (by linarith)
    unfold aklvAccuracyLogCoefficient aklvInitialRankLogCoefficient
    positivity
  exact hfourth.trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl _) hlinear) hC)

/-- LVV form of the AKLV per-cut rank estimate: the logarithm of the rank is
linear in `log (128 / rho)`, with coefficient proportional to `u³ / g`. -/
theorem aklvAccuracyRankBound_log_le_lvv {A g rho : ℝ}
    (hA : 1 ≤ A) (hg : 0 < g) (hg1 : g ≤ 1) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (q : ℕ) (hq : 2 ≤ q) :
    let u := 1 + log (q : ℝ) + log (1 / g)
    let z := aklvAccuracyLog rho
    let s0 : ℕ := ⌈A * u ^ 2 / g⌉₊
    log (aklvAccuracyRankBound q s0 g rho : ℝ) ≤
      11 * aklvAccuracyLogCoefficient A * (u ^ 3 / g) * z := by
  intro u z s0
  have hu : 1 ≤ u := by
    have hqlog : 0 ≤ log (q : ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
    have hglog : 0 ≤ log (1 / g) := log_nonneg ((one_le_div hg).mpr hg1)
    dsimp only [u]
    linarith
  have hz : 1 ≤ z := (aklvAccuracyLog_bounds hrho hrho1).1
  have hlinear := aklvAccuracyRankBound_log_le_linear hA hg hg1 hrho hrho1 q hq
  change log (aklvAccuracyRankBound q s0 g rho : ℝ) ≤
    aklvAccuracyLogCoefficient A *
      (u ^ 3 / g + sqrt (sqrt (2 / g)) * (u + 4) * z) at hlinear
  have hx : 1 ≤ 2 / g := by
    apply (le_div_iff₀ hg).2
    linarith
  have hsqrt : sqrt (sqrt (2 / g)) ≤ 2 / g := by
    exact (sqrt_le_self_iff.mpr (Or.inr (one_le_sqrt.mpr hx))).trans
      (sqrt_le_self_iff.mpr (Or.inr hx))
  have hcoef : sqrt (sqrt (2 / g)) * (u + 4) ≤ 10 * u ^ 3 / g := by
    have hmul := mul_le_mul_of_nonneg_right hsqrt (by linarith : 0 ≤ u + 4)
    rw [show 2 / g * (u + 4) = (2 * (u + 4)) / g by field_simp] at hmul
    refine hmul.trans ((div_le_div_iff_of_pos_right hg).2 ?_)
    have hcubic : u + 4 ≤ 5 * u ^ 3 := by
      nlinarith [sq_nonneg (u - 1),
        mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hu)]
    linarith
  have hinside :
      u ^ 3 / g + sqrt (sqrt (2 / g)) * (u + 4) * z ≤
        11 * (u ^ 3 / g) * z := by
    have hfirst : u ^ 3 / g ≤ u ^ 3 / g * z := by
      exact le_mul_of_one_le_right (by positivity) hz
    have hsecond := mul_le_mul_of_nonneg_right hcoef (by linarith : 0 ≤ z)
    calc
      _ ≤ u ^ 3 / g * z + 10 * u ^ 3 / g * z := add_le_add hfirst hsecond
      _ = 11 * (u ^ 3 / g) * z := by ring
  have hC : 0 ≤ aklvAccuracyLogCoefficient A := by
    have hlog : 0 ≤ log (A + 1) := log_nonneg (by linarith)
    unfold aklvAccuracyLogCoefficient aklvInitialRankLogCoefficient
    positivity
  calc
    _ ≤ aklvAccuracyLogCoefficient A *
        (u ^ 3 / g + sqrt (sqrt (2 / g)) * (u + 4) * z) := hlinear
    _ ≤ aklvAccuracyLogCoefficient A * (11 * (u ^ 3 / g) * z) :=
      mul_le_mul_of_nonneg_left hinside hC
    _ = 11 * aklvAccuracyLogCoefficient A * (u ^ 3 / g) * z := by ring

/-- Sharpened LVV form of the selected rank estimate. The coefficient has the
cubic local-dimension dependence of the source and only one additional factor
of `log (1 / g)`. This is a scalar estimate for the selected rank budget, not
a physical approximation theorem at the smaller initial width. -/
theorem aklvAccuracyRankBound_log_le_lvv_separated {A g rho : ℝ}
    (hA : 1 ≤ A) (hg : 0 < g) (hg1 : g ≤ 1) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (q : ℕ) (hq : 2 ≤ q) :
    let v := 1 + log (q : ℝ)
    let w := log (1 / g)
    let z := aklvAccuracyLog rho
    let s0 : ℕ := ⌈A * v ^ 2 / g⌉₊
    log (aklvAccuracyRankBound q s0 g rho : ℝ) ≤
      11 * aklvAccuracyLogCoefficient A * ((v ^ 3 + v ^ 2 * w) / g) * z := by
  intro v w z s0
  have hv : 1 ≤ v := by
    have hqlog : 0 ≤ log (q : ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
    dsimp only [v]
    linarith
  have hw : 0 ≤ w := by
    dsimp only [w]
    exact log_nonneg ((one_le_div hg).mpr hg1)
  have hz : 1 ≤ z := (aklvAccuracyLog_bounds hrho hrho1).1
  have hfourth := aklvAccuracyRankBound_log_le_fourthRoot_separated
    hA hg hg1 hrho hrho1 q hq
  change log (aklvAccuracyRankBound q s0 g rho : ℝ) ≤
    aklvAccuracyLogCoefficient A *
      ((v ^ 3 + v ^ 2 * w) / g +
        sqrt (sqrt (z ^ 3 / g)) * (v + log (z + 1))) at hfourth
  have haccuracy := aklv_fourthRoot_accuracy_cost_le_linear (by linarith : 0 ≤ v) hg hz
  let X := (v ^ 3 + v ^ 2 * w) / g
  have hX : 0 ≤ X := by dsimp only [X]; positivity
  have hvX : v ^ 3 / g ≤ X := by
    dsimp only [X]
    rw [add_div]
    exact le_add_of_nonneg_right (div_nonneg (mul_nonneg (sq_nonneg v) hw) hg.le)
  have hx : 1 ≤ 2 / g := by
    apply (le_div_iff₀ hg).2
    linarith
  have hsqrt : sqrt (sqrt (2 / g)) ≤ 2 / g := by
    exact (sqrt_le_self_iff.mpr (Or.inr (one_le_sqrt.mpr hx))).trans
      (sqrt_le_self_iff.mpr (Or.inr hx))
  have hcoef : sqrt (sqrt (2 / g)) * (v + 4) ≤ 10 * v ^ 3 / g := by
    have hmul := mul_le_mul_of_nonneg_right hsqrt (by linarith : 0 ≤ v + 4)
    rw [show 2 / g * (v + 4) = (2 * (v + 4)) / g by field_simp] at hmul
    refine hmul.trans ((div_le_div_iff_of_pos_right hg).2 ?_)
    have hcubic : v + 4 ≤ 5 * v ^ 3 := by
      nlinarith [sq_nonneg (v - 1),
        mul_nonneg (sq_nonneg v) (sub_nonneg.mpr hv)]
    linarith
  have hcoefX : sqrt (sqrt (2 / g)) * (v + 4) ≤ 10 * X := by
    calc
      _ ≤ 10 * v ^ 3 / g := hcoef
      _ = 10 * (v ^ 3 / g) := by ring
      _ ≤ 10 * X := mul_le_mul_of_nonneg_left hvX (by norm_num)
  have hinside : X + sqrt (sqrt (z ^ 3 / g)) * (v + log (z + 1)) ≤
      11 * X * z := by
    have hfirst : X ≤ X * z := le_mul_of_one_le_right hX hz
    have hsecond := haccuracy.trans
      (mul_le_mul_of_nonneg_right hcoefX (by linarith : 0 ≤ z))
    nlinarith only [hfirst, hsecond]
  have hC : 0 ≤ aklvAccuracyLogCoefficient A := by
    have hlog : 0 ≤ log (A + 1) := log_nonneg (by linarith)
    unfold aklvAccuracyLogCoefficient aklvInitialRankLogCoefficient
    positivity
  change log (aklvAccuracyRankBound q s0 g rho : ℝ) ≤
    11 * aklvAccuracyLogCoefficient A * X * z
  calc
    _ ≤ aklvAccuracyLogCoefficient A *
        (X + sqrt (sqrt (z ^ 3 / g)) * (v + log (z + 1))) := hfourth
    _ ≤ aklvAccuracyLogCoefficient A * (11 * X * z) :=
      mul_le_mul_of_nonneg_left hinside hC
    _ = 11 * aklvAccuracyLogCoefficient A * X * z := by ring

/-- On any interval of gaps bounded away from zero, the proved AKLV coefficient has the
printed cubic dependence on the logarithm of the local dimension.  The comparison constant
depends explicitly on the chosen lower gap bound; it is therefore compatible with, and does
not weaken, `aklv_gap_logarithm_not_uniformly_absorbable` below. -/
theorem aklv_cubic_cost_of_fixed_gap {g₀ g : ℝ} (hg₀ : 0 < g₀) (hg₀one : g₀ ≤ 1)
    (hg₀g : g₀ ≤ g) (hg : 0 < g) (hg1 : g ≤ 1) (q : ℕ) (hq : 2 ≤ q) :
    let u := 1 + log (q : ℝ) + log (1 / g)
    let C := ((1 + 1 / log 2) * (1 + log (1 / g₀))) ^ 3
    u ^ 3 / g ≤ C * log (q : ℝ) ^ 3 / g := by
  intro u C
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hlogq : log (2 : ℝ) ≤ log (q : ℝ) :=
    log_le_log (by norm_num) (by exact_mod_cast hq)
  have hlogq0 : 0 ≤ log (q : ℝ) := hlog2.le.trans hlogq
  have hone : 1 ≤ log (q : ℝ) / log 2 :=
    (le_div_iff₀ hlog2).2 (by simpa using hlogq)
  let v := 1 + log (q : ℝ)
  let c := 1 + 1 / log 2
  have hv : 0 ≤ v := by dsimp only [v]; linarith
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hvle : v ≤ c * log (q : ℝ) := by
    dsimp only [v, c]
    calc
      1 + log (q : ℝ) ≤ log (q : ℝ) / log 2 + log (q : ℝ) :=
        by simpa [add_comm] using add_le_add_right hone (log (q : ℝ))
      _ = (1 + 1 / log 2) * log (q : ℝ) := by ring
  have hw₀ : 0 ≤ log (1 / g₀) := log_nonneg ((one_le_div hg₀).mpr hg₀one)
  have hinv : 1 / g ≤ 1 / g₀ := one_div_le_one_div_of_le hg₀ hg₀g
  have hw : log (1 / g) ≤ log (1 / g₀) :=
    log_le_log (by positivity) hinv
  have hule : u ≤ (1 + log (1 / g₀)) * v := by
    dsimp only [u, v]
    nlinarith [mul_le_mul_of_nonneg_left (show 1 ≤ v by
      dsimp only [v]; linarith) hw₀]
  have hu0 : 0 ≤ u := by
    dsimp only [u]
    have hgw : 0 ≤ log (1 / g) := log_nonneg ((one_le_div hg).mpr hg1)
    linarith
  have hfactor : 0 ≤ 1 + log (1 / g₀) := by linarith
  have hcombined : u ≤ (1 + log (1 / g₀)) * c * log (q : ℝ) :=
    hule.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hvle hfactor)
  have hpow := pow_le_pow_left₀ hu0 hcombined 3
  dsimp only [C, c] at hpow ⊢
  exact div_le_div_of_nonneg_right (by nlinarith only [hpow]) hg.le

/-- The gap logarithm in the proved AKLV coefficient cannot be absorbed into
a universal multiple of `log 2 ³`. Thus passing from the formal `u³ / g`
coefficient to the printed `log³ q / g` dependence requires a genuinely
sharper estimate, not a change of universal constant. -/
theorem aklv_gap_logarithm_not_uniformly_absorbable (K : ℝ) (hK : 0 ≤ K) :
    ∃ g : ℝ, 0 < g ∧ g ≤ 1 ∧
      K * log (2 : ℝ) ^ 3 <
        (1 + log (2 : ℝ) + log (1 / g)) ^ 3 := by
  let x := K * log (2 : ℝ) ^ 3
  let g := exp (-(x + 1))
  have hlog2 : 0 ≤ log (2 : ℝ) := log_nonneg (by norm_num)
  have hx : 0 ≤ x := by dsimp only [x]; positivity
  have hg : 0 < g := by dsimp only [g]; positivity
  have hg1 : g ≤ 1 := by
    rw [show (1 : ℝ) = exp 0 by simp]
    exact exp_le_exp.mpr (by linarith)
  have hloginv : log (1 / g) = x + 1 := by
    dsimp only [g]
    rw [one_div, ← exp_neg, log_exp]
    ring
  refine ⟨g, hg, hg1, ?_⟩
  rw [hloginv]
  change x < (1 + log (2 : ℝ) + (x + 1)) ^ 3
  let y := 1 + log (2 : ℝ) + (x + 1)
  have hy : 1 ≤ y := by dsimp only [y]; linarith
  have hy3 : y ≤ y ^ 3 := by
    nlinarith [sq_nonneg y, mul_nonneg (sq_nonneg y) (sub_nonneg.mpr hy)]
  dsimp only [y] at hy3 ⊢
  linarith

end TNLean.MPS.AreaLaw

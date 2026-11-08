/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.OptimizedRankLog

/-!
# Uniform bounds for the initial AKLV width

The scalar estimates are independent of the existence of a fitting physical
window. They apply to every universal coefficient at least one and provide
the scale comparisons needed by the accuracy-dependent rank argument.

Source: AKLV, arXiv:1301.1162v1, lines 1016--1024 and 1503--1517.
-/

open Real

namespace TNLean.MPS.AreaLaw

/-- A conservative universal coefficient for the initial logarithmic rank. -/
noncomputable def aklvInitialRankLogCoefficient (A : ℝ) : ℝ :=
  100 * (A + 1) * (8 + 2 * log (A + 1))

/-- Initial-width bounds hold without a chain length or a fitting-window
premise. In particular they supply every auxiliary scale premise in the
sharp accuracy-dependent degree comparison. -/
theorem aklv_initial_width_bounds {A g : ℝ} (hA : 1 ≤ A) (hg : 0 < g) (hg1 : g ≤ 1)
    (q : ℕ) (hq : 1 ≤ q) :
    let u := 1 + log (q : ℝ) + log (1 / g)
    let s0 : ℕ := ⌈A * u ^ 2 / g⌉₊
    1 ≤ u ∧ 1 ≤ s0 ∧ 1 / g ≤ (s0 : ℝ) ∧ log (1 / g) ≤ (s0 : ℝ) ∧
      aklvLogarithmicThreshold g ≤ 1040 * (s0 : ℝ) ∧
      (s0 : ℝ) ≤ (A + 1) * u ^ 2 / g ∧
      log (((q * (s0 ^ 2 + 1)) ^ (32 * (2 * s0 + 1)) : ℕ) : ℝ) ≤
        aklvInitialRankLogCoefficient A / g * u ^ 3 := by
  intro u s0
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hqlog : 0 ≤ log (q : ℝ) := log_nonneg (by exact_mod_cast hq)
  have hglog : 0 ≤ log (1 / g) := log_nonneg ((one_le_div hg).mpr hg1)
  have hu : 1 ≤ u := by dsimp only [u]; linarith
  have hupos : 0 < u := by linarith
  have hAu : 1 ≤ A * u ^ 2 := by
    have h := mul_le_mul hA (one_le_pow₀ hu : 1 ≤ u ^ 2) zero_le_one (by linarith : 0 ≤ A)
    simpa only [one_mul] using h
  have hlower : A * u ^ 2 / g ≤ (s0 : ℝ) := Nat.le_ceil _
  have hgap : 1 / g ≤ (s0 : ℝ) :=
    (div_le_div_of_nonneg_right hAu hg.le).trans hlower
  have hs01R : (1 : ℝ) ≤ s0 := ((one_le_div hg).mpr hg1).trans hgap
  have hs01 : 1 ≤ s0 := by exact_mod_cast hs01R
  have hs0pos : 0 < (s0 : ℝ) := by linarith
  have hglogS : log (1 / g) ≤ (s0 : ℝ) := by
    calc
      log (1 / g) ≤ u ^ 2 := by dsimp only [u] at hu ⊢; nlinarith
      _ ≤ A * u ^ 2 / g := (le_div_iff₀ hg).mpr
        (by nlinarith only [mul_le_mul_of_nonneg_right (hg1.trans hA) (sq_nonneg u)])
      _ ≤ (s0 : ℝ) := hlower
  have hT : aklvLogarithmicThreshold g ≤ 1040 * (s0 : ℝ) := by
    unfold aklvLogarithmicThreshold
    linarith
  have hUs : 1 ≤ u ^ 2 / g := (le_div_iff₀ hg).mpr
    (by nlinarith only [hg1, (one_le_pow₀ hu : 1 ≤ u ^ 2)])
  have hupper : (s0 : ℝ) ≤ (A + 1) * u ^ 2 / g := by
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ A * u ^ 2 / g by positivity)
    change (s0 : ℝ) < A * u ^ 2 / g + 1 at hceil
    calc
      (s0 : ℝ) ≤ A * u ^ 2 / g + 1 := hceil.le
      _ ≤ A * u ^ 2 / g + u ^ 2 / g := by linarith only [hUs]
      _ = (A + 1) * u ^ 2 / g := by ring
  refine ⟨hu, hs01, hgap, hglogS, hT, hupper, ?_⟩
  have hAlog : 0 ≤ log (A + 1) := log_nonneg (by linarith)
  have hlogS : log (s0 : ℝ) ≤ (3 + log (A + 1)) * u := by
    have h := log_le_log hs0pos hupper
    rw [log_div (by positivity) (ne_of_gt hg),
      log_mul (by positivity) (by positivity), log_pow] at h
    have hlogu : log u ≤ u := (log_le_sub_one_of_pos hupos).trans (by linarith)
    have hlogg : log (1 / g) ≤ u := by dsimp only [u]; linarith
    have hloggEq : log (1 / g) = -log g := by rw [one_div, log_inv]
    have hAlogu := mul_le_mul_of_nonneg_left hu hAlog
    norm_num only [Nat.cast_ofNat] at h
    rw [sub_eq_add_neg, ← hloggEq] at h
    nlinarith
  let b := (q : ℝ) * ((s0 : ℝ) ^ 2 + 1)
  have hb : 0 < b := by dsimp only [b]; positivity
  have hbase : log b ≤ (8 + 2 * log (A + 1)) * u := by
    have hbup : b ≤ (q : ℝ) * (2 * (s0 : ℝ) ^ 2) := by
      dsimp only [b]
      nlinarith only [mul_nonneg hqpos.le (show 0 ≤ (s0 : ℝ) ^ 2 - 1 by nlinarith)]
    have h := log_le_log hb hbup
    have hright : log ((q : ℝ) * (2 * (s0 : ℝ) ^ 2)) =
        log (q : ℝ) + log 2 + 2 * log (s0 : ℝ) := by
      rw [log_mul (ne_of_gt hqpos) (by positivity),
        log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity), log_pow]
      norm_num
      ring
    rw [hright] at h
    have hlogq : log (q : ℝ) ≤ u := by dsimp only [u]; linarith
    have hlog2 : log (2 : ℝ) ≤ 1 := by
      have h := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h
      exact h
    nlinarith
  have hbase0 : 0 ≤ log b := by
    apply log_nonneg
    dsimp only [b]
    have hsquare : 1 ≤ (s0 : ℝ) ^ 2 + 1 := by nlinarith only [sq_nonneg (s0 : ℝ)]
    nlinarith only [mul_le_mul_of_nonneg_left hsquare hqpos.le,
      (show 1 ≤ (q : ℝ) by exact_mod_cast hq)]
  rw [Nat.cast_pow, log_pow]
  push_cast
  change (32 * (2 * (s0 : ℝ) + 1)) * log b ≤ _
  calc
    _ ≤ 96 * (s0 : ℝ) * log b := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hs01R) hbase0]
    _ ≤ 96 * (s0 : ℝ) * ((8 + 2 * log (A + 1)) * u) :=
      mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = (96 * (8 + 2 * log (A + 1)) * u) * (s0 : ℝ) := by ring
    _ ≤ (96 * (8 + 2 * log (A + 1)) * u) * ((A + 1) * u ^ 2 / g) :=
      mul_le_mul_of_nonneg_left hupper (by positivity)
    _ = 96 * (A + 1) * (8 + 2 * log (A + 1)) / g * u ^ 3 := by ring
    _ ≤ aklvInitialRankLogCoefficient A / g * u ^ 3 := by
      unfold aklvInitialRankLogCoefficient
      gcongr
      norm_num

end TNLean.MPS.AreaLaw

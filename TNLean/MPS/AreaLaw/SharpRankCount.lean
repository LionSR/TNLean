/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.SharpApproximationParameters

/-!
# Logarithmic counts at the independent approximation scales

The exact polynomial-family count is estimated without replacing its
fourth-root window by the coarser entropy scale. These estimates support
ALVV, arXiv:1602.08828v2, Theorem 4.9, proof line 1080.
-/

namespace Real

/-- The logarithm of the actual polynomial-family count retains the
quarter-power gap and three-quarter-power accuracy terms of its window.
The additional factor is logarithmic in the logarithmic accuracy variable.
Auxiliary to ALVV, arXiv:1602.08828v2, Theorem 4.9, proof line 1080. -/
theorem sharp_polynomial_family_log_count
    (q ell : ℕ) (g a b : ℝ) (hq : 1 ≤ q) (hell : 1 ≤ ell)
    (hg : 0 < g) (hg1 : g ≤ 1) (ha : 1 ≤ a) (hb : 0 ≤ b)
    (hwindow : (ell : ℝ) ≤ 10 / g + b * (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ)) :
    let u := 1 + log (q : ℝ) + log (1 / g)
    log (((q * ell ^ 2) ^ (22 * ell) : ℕ) : ℝ) ≤
      44 * (1 + log (11 + b)) *
        (10 / g + b * (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ)) *
        u * (1 + log a) := by
  intro u
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hellpos : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast (by omega : 0 < ell)
  have hapos : 0 < a := zero_lt_one.trans_le ha
  have hinv : 1 ≤ 1 / g := (one_le_div hg).2 hg1
  have hinvpos : 0 < 1 / g := one_div_pos.mpr hg
  have hrootg : (1 / g) ^ (1 / 4 : ℝ) ≤ 1 / g := by
    simpa only [rpow_one] using
      rpow_le_rpow_of_exponent_le hinv (by norm_num : (1 / 4 : ℝ) ≤ 1)
  have hroota : a ^ (3 / 4 : ℝ) ≤ a := by
    simpa only [rpow_one] using
      rpow_le_rpow_of_exponent_le ha (by norm_num : (3 / 4 : ℝ) ≤ 1)
  have hproduct : (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) ≤ (1 / g) * a :=
    mul_le_mul hrootg hroota (rpow_nonneg hapos.le _) hinvpos.le
  have hcoarse : (ell : ℝ) ≤ (11 + b) * (1 / g) * a := by
    calc
      (ell : ℝ) ≤ 10 / g + b *
          ((1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ)) := by
        simpa only [mul_assoc] using hwindow
      _ ≤ 10 / g + b * ((1 / g) * a) :=
        by linarith only [mul_le_mul_of_nonneg_left hproduct hb]
      _ = 10 * (1 / g) + b * ((1 / g) * a) := by ring
      _ ≤ (11 + b) * (1 / g) * a := by
        have hten := mul_le_mul_of_nonneg_left ha (show 0 ≤ 10 * (1 / g) by positivity)
        nlinarith only [hten, mul_nonneg hinvpos.le hapos.le]
  have hKpos : 0 < 11 + b := by linarith only [hb]
  have hlogK : 0 ≤ log (11 + b) := log_nonneg (by linarith only [hb])
  have hlogell : log (ell : ℝ) ≤ log (11 + b) + log (1 / g) + log a := by
    have h := log_le_log hellpos hcoarse
    rw [log_mul (mul_pos hKpos hinvpos).ne' hapos.ne', log_mul hKpos.ne' hinvpos.ne'] at h
    exact h
  have hlogq : 0 ≤ log (q : ℝ) := log_nonneg (by exact_mod_cast hq)
  have hlogg : 0 ≤ log (1 / g) := log_nonneg hinv
  have hloga : 0 ≤ log a := log_nonneg ha
  have hu : 1 ≤ u := by dsimp only [u]; linarith only [hlogq, hlogg]
  have hlogbase : log (q : ℝ) + 2 * log (ell : ℝ) ≤
      2 * (1 + log (11 + b)) * u * (1 + log a) := by
    have huEq : u = 1 + log (q : ℝ) + log (1 / g) := rfl
    have hfirst : log (q : ℝ) + 2 * log (ell : ℝ) ≤
        2 * (1 + log (11 + b)) * (u + log a) := by
      nlinarith only [hlogell, huEq, hlogq,
        mul_nonneg hlogK (sub_nonneg.mpr hu), mul_nonneg hlogK hloga]
    have hlast : u + log a ≤ u * (1 + log a) := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hu) hloga]
    calc
      _ ≤ 2 * (1 + log (11 + b)) * (u + log a) := hfirst
      _ ≤ 2 * (1 + log (11 + b)) * (u * (1 + log a)) :=
        mul_le_mul_of_nonneg_left hlast (by positivity)
      _ = _ := by ring
  have hidentity : log (((q * ell ^ 2) ^ (22 * ell) : ℕ) : ℝ) =
      22 * (ell : ℝ) * (log (q : ℝ) + 2 * log (ell : ℝ)) := by
    simp only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, log_pow]
    rw [log_mul hqpos.ne' (pow_pos hellpos 2).ne', log_pow]
    norm_num only [Nat.cast_ofNat]
  rw [hidentity]
  calc
    _ ≤ 22 * (ell : ℝ) * (2 * (1 + log (11 + b)) * u * (1 + log a)) :=
      mul_le_mul_of_nonneg_left hlogbase (by positivity)
    _ = (44 * (1 + log (11 + b)) * u * (1 + log a)) * (ell : ℝ) := by ring
    _ ≤ (44 * (1 + log (11 + b)) * u * (1 + log a)) *
        (10 / g + b * (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left hwindow (by positivity)
    _ = _ := by ring

/-- A bootstrap count and the independent polynomial count give a logarithmic
rank budget with coefficient one on the logarithm of the target dimension.
The only additional accuracy factor is `1 + log a`. Auxiliary to ALVV,
arXiv:1602.08828v2, Theorem 4.9, fixed-cut rank estimate. -/
theorem sharp_approximation_log_rank_budget
    (r D0 q ell : ℕ) (g a K0 b : ℝ)
    (hr : 1 ≤ r) (hD0 : 1 ≤ D0) (hq : 1 ≤ q) (hell : 1 ≤ ell)
    (hg : 0 < g) (hg1 : g ≤ 1) (ha : 1 ≤ a) (hK0 : 0 ≤ K0) (hb : 0 ≤ b)
    (hwindow : (ell : ℝ) ≤ 10 / g + b * (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ))
    (hbootstrap : log (D0 : ℝ) ≤ K0 / g *
      (1 + log (q : ℝ) + log (1 / g)) ^ 3) :
    let u := 1 + log (q : ℝ) + log (1 / g)
    let D1 : ℕ := (q * ell ^ 2) ^ (22 * ell)
    log ((r * D0 ^ 24 * D1 ^ 2 : ℕ) : ℝ) ≤ log (r : ℝ) +
      (24 * K0 + 88 * (1 + log (11 + b)) * (11 + b)) *
        (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) * u) * (1 + log a) := by
  intro u D1
  let X := u ^ 3 / g
  let Y := (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) * u
  let P := 1 + log a
  let kappa := 44 * (1 + log (11 + b))
  have hlogq : 0 ≤ log (q : ℝ) := log_nonneg (by exact_mod_cast hq)
  have hlogg : 0 ≤ log (1 / g) := log_nonneg ((one_le_div hg).2 hg1)
  have hu : 1 ≤ u := by dsimp only [u]; linarith only [hlogq, hlogg]
  have hu0 : 0 ≤ u := zero_le_one.trans hu
  have hloga : 0 ≤ log a := log_nonneg ha
  have hP : 1 ≤ P := by dsimp only [P]; linarith only [hloga]
  have hkappa : 0 ≤ kappa := by
    have hlogb : 0 ≤ log (11 + b) := log_nonneg (by linarith only [hb])
    dsimp only [kappa]
    positivity
  have hX : 0 ≤ X := by dsimp only [X]; positivity
  have hY : 0 ≤ Y := by dsimp only [Y]; positivity
  have hucube : u ≤ u ^ 3 := by
    have hu2 : 1 ≤ u ^ 2 := by nlinarith only [hu]
    nlinarith only [mul_le_mul_of_nonneg_left hu2 hu0]
  have huX : u / g ≤ X := div_le_div_of_nonneg_right hucube hg.le
  have hcount : log (D1 : ℝ) ≤ kappa *
      (10 / g + b * (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ)) * u * P :=
    sharp_polynomial_family_log_count q ell g a b hq hell hg hg1 ha hb hwindow
  have hcountpoly :
      (10 / g + b * (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ)) * u ≤
        (11 + b) * (X + Y) := by
    calc
      _ = 10 * (u / g) + b * Y := by dsimp only [Y]; ring
      _ ≤ 10 * X + b * Y := by linarith only [huX]
      _ ≤ (11 + b) * (X + Y) := by
        nlinarith only [hX, hY, mul_nonneg hb hX]
  have hcountgrow : 2 * log (D1 : ℝ) ≤
      2 * kappa * (11 + b) * (X + Y) * P := by
    have hscale := mul_le_mul_of_nonneg_left hcountpoly hkappa
    have hscaleP := mul_le_mul_of_nonneg_right hscale (zero_le_one.trans hP)
    nlinarith only [hcount, hscaleP]
  have hXgrow : X ≤ (X + Y) * P := by
    nlinarith only [hY, mul_nonneg (add_nonneg hX hY) (sub_nonneg.mpr hP)]
  have hbasegrow : 24 * log (D0 : ℝ) ≤ 24 * K0 * (X + Y) * P := by
    have hbase : log (D0 : ℝ) ≤ K0 * X := by
      calc
        _ ≤ K0 / g * u ^ 3 := hbootstrap
        _ = K0 * X := by dsimp only [X]; ring
    have hscale := mul_le_mul_of_nonneg_left hXgrow hK0
    nlinarith only [hbase, hscale]
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hD0pos : (0 : ℝ) < (D0 : ℝ) := by exact_mod_cast (by omega : 0 < D0)
  have hD1posN : 0 < D1 := by dsimp only [D1]; positivity
  have hD1pos : (0 : ℝ) < (D1 : ℝ) := by exact_mod_cast hD1posN
  have hidentity : log ((r * D0 ^ 24 * D1 ^ 2 : ℕ) : ℝ) =
      log (r : ℝ) + 24 * log (D0 : ℝ) + 2 * log (D1 : ℝ) := by
    simp only [Nat.cast_mul, Nat.cast_pow]
    rw [log_mul (mul_pos hrpos (pow_pos hD0pos 24)).ne' (pow_pos hD1pos 2).ne',
      log_mul hrpos.ne' (pow_pos hD0pos 24).ne', log_pow, log_pow]
    norm_num only [Nat.cast_ofNat]
  rw [hidentity]
  calc
    _ ≤ log (r : ℝ) + 24 * K0 * (X + Y) * P +
        2 * kappa * (11 + b) * (X + Y) * P := by
      linarith only [hbasegrow, hcountgrow]
    _ = _ := by dsimp only [X, Y, P, kappa]; ring

end Real

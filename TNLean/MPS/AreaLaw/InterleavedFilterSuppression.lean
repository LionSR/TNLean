/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.InterleavedTruncationCalibration

/-!
# Suppression at the actual interleaved count

The tiny target accuracy determines an independent clipping threshold.
Its width is bounded in terms of the same polynomial-family count and
sampling size used to define that accuracy. These scalar estimates
support ALVV, arXiv:1602.08828v2, Theorem `t:ais`, lines 1010–1024,
and the interleaved parameter selection, lines 1797–1805.
-/

namespace Real

/-- A numerical logarithmic margin reserves a factor two in the count
tradeoff. Scalar auxiliary for ALVV, arXiv:1602.08828v2, lines 1010–1024. -/
private theorem log_filter_margin_le : log (800000 : ℝ) ≤ 20 := by
  have hlog2 : log 2 ≤ 1 := by
    have h := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  calc
    log (800000 : ℝ) ≤ log ((2 : ℝ) ^ 20) := log_le_log (by norm_num) (by norm_num)
    _ = 20 * log 2 := log_pow 2 20
    _ ≤ _ := by linarith only [hlog2]

/-- The actual tiny-overlap truncation threshold has the required width
bound at the same count. The displayed numerical identities are
subsequently derived from the explicit window and sample ceilings.
Supporting ALVV, arXiv:1602.08828v2, lines 1010–1024 and 1797–1805. -/
theorem interleaved_threshold_width_bounds
    (Ctail g w E B : ℝ) (D s : ℕ)
    (hCtail : 21 ≤ Ctail) (hg : 0 < g) (hg1 : g ≤ 1)
    (hw : 1 ≤ w) (hE : 1 ≤ E) (hB : 1 ≤ B) (hD : 2 ≤ D) (hs : 1 ≤ s)
    (hcount : log (D : ℝ) = 22 * E * B)
    (hgapLog : 1 + log (1 / g) ≤ E * B)
    (hsLog : log (s : ℝ) ≤ 13 * (log (D : ℝ) + w)) :
    let a := 3 / (32 * (D : ℝ) ^ 12 * (s : ℝ) ^ 5)
    let tau := a ^ 2 / 1048576
    let t := Ctail * (1 + log (1 / g) + log (1 / tau))
    21 ≤ t ∧ 3 * log (D : ℝ) + log 800000 / 4 ≤ t ∧
      t ≤ 4000 * Ctail * (E * B + w) := by
  intro a tau t
  have hC0 : 0 ≤ Ctail := by linarith
  have hlogD : 0 ≤ log (D : ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ D by omega))
  have hlogg : 0 ≤ log (1 / g) := log_nonneg ((one_le_div hg).mpr hg1)
  obtain ⟨hlower, hupper⟩ := interleaved_accuracy_log_bounds D s hD hs
  change 24 * log (D : ℝ) ≤ log (1 / tau) at hlower
  change log (1 / tau) ≤ 28 + 24 * log (D : ℝ) + 10 * log (s : ℝ) at hupper
  have hlog800000 := log_filter_margin_le
  have hinner : 1 + 24 * log (D : ℝ) ≤ 1 + log (1 / g) + log (1 / tau) := by
    linarith only [hlower, hlogg]
  have htlower : 21 * (1 + 24 * log (D : ℝ)) ≤ t :=
    mul_le_mul hCtail hinner (by linarith only [hlogD]) hC0
  have ht21 : 21 ≤ t := by nlinarith only [htlower, hlogD]
  have htPower : 3 * log (D : ℝ) + log 800000 / 4 ≤ t := by
    nlinarith only [htlower, hlogD, hlog800000]
  refine ⟨ht21, htPower, ?_⟩
  have hEB : 1 ≤ E * B := one_le_mul_of_one_le_of_one_le hE hB
  have hinnerUp : 1 + log (1 / g) + log (1 / tau) ≤ 4000 * (E * B + w) := by
    nlinarith only [hupper, hsLog, hgapLog, hcount, hEB, hw]
  calc
    t ≤ Ctail * (4000 * (E * B + w)) := mul_le_mul_of_nonneg_left hinnerUp hC0
    _ = _ := by ring

/-- The sampling and independent window ceilings derive every numerical
premise of the threshold-width estimate at the same count. There is no
supplied count, overlap, or logarithmic-size bound. Supporting ALVV,
arXiv:1602.08828v2, lines 1010–1024 and 1797–1805. -/
theorem interleaved_actual_threshold_width_bounds
    (Ctail C : ℝ) (m r L : ℕ) (g : ℝ)
    (hCtail : 21 ≤ Ctail) (hC : 21 ≤ C) (hm : 50 ≤ m) (hr : 1 ≤ r)
    (hg : 0 < g) (hg1 : g ≤ 1) :
    let w := 1 + log (r : ℝ) + 2 * log ((L : ℝ) + 1)
    let v := 1 + log (m : ℝ) + log (1 / g) + log (1 + w)
    let ell := Nat.ceil (C * (v ^ 6 / g + sqrt w * v ^ 3 / sqrt g))
    let D := (m * ell ^ 2) ^ (22 * ell)
    let A := log (D : ℝ) + w
    let s := Nat.ceil (4096 * (r : ℝ) * A)
    let a := 3 / (32 * (D : ℝ) ^ 12 * (s : ℝ) ^ 5)
    let tau := a ^ 2 / 1048576
    let t := Ctail * (1 + log (1 / g) + log (1 / tau))
    let B := log ((m : ℝ) * (ell : ℝ) ^ 2)
    1 ≤ w ∧ 21 ≤ ell ∧ 2 ≤ D ∧ 1 ≤ s ∧ 1 ≤ B ∧
      log (D : ℝ) = 22 * (ell : ℝ) * B ∧
      21 ≤ t ∧ 3 * log (D : ℝ) + log 800000 / 4 ≤ t ∧
      t ≤ 4000 * Ctail * ((ell : ℝ) * B + w) := by
  intro w v ell D A s a tau t B
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hL : 0 ≤ (L : ℝ) := Nat.cast_nonneg _
  have hlogr : 0 ≤ log (r : ℝ) := log_nonneg hrR
  have hlogL : 0 ≤ log ((L : ℝ) + 1) := log_nonneg (by linarith only [hL])
  have hw : 1 ≤ w := by dsimp only [w]; linarith
  obtain ⟨hell, hfirst, _hsecond, _hupper, _hbase, _hlogD⟩ :=
    interleaved_filter_scale_count_bounds C m g w hC hm hg hg1 hw
  change 21 ≤ ell at hell
  have hell0 : 0 ≤ (ell : ℝ) := Nat.cast_nonneg _
  have hellR : (21 : ℝ) ≤ ell := by exact_mod_cast hell
  have hellpos : (0 : ℝ) < ell := by linarith
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
  have hmPos : (0 : ℝ) < m := by linarith
  have hbase2 : 2 ≤ m * ell ^ 2 := by
    have hsq : 1 ≤ ell ^ 2 := Nat.one_le_pow 2 ell (by omega)
    nlinarith only [hm, hsq]
  have hD : 2 ≤ D := Nat.one_lt_pow (by omega : 22 * ell ≠ 0) (by omega)
  obtain ⟨_hw, hs, _hsUpper, hsLog⟩ := interleaved_sample_size_bounds r L D hr hD
  have hlogm : 0 ≤ log (m : ℝ) := log_nonneg (by linarith)
  have hlogw : 0 ≤ log (1 + w) := log_nonneg (by linarith)
  have hv : 1 ≤ v := one_le_interleaved_log_scale m g w hmR hg hg1 hw
  have hv0 : 0 ≤ v := by linarith
  have hInv : (ell : ℝ)⁻¹ ≤ 1 / 2 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ ell by linarith)
    simpa only [one_div] using h
  have hlogEll := one_sub_inv_le_log_of_pos hellpos
  have hBexp : B = log (m : ℝ) + 2 * log (ell : ℝ) := by
    dsimp only [B]
    rw [log_mul hmPos.ne' (pow_ne_zero 2 hellpos.ne'), log_pow]
    norm_num
  have hB : 1 ≤ B := by rw [hBexp]; linarith only [hlogm, hlogEll, hInv]
  have hDcast : (D : ℝ) = ((m : ℝ) * (ell : ℝ) ^ 2) ^ (22 * ell) := by
    simp only [D, Nat.cast_pow, Nat.cast_mul]
  have hcount : log (D : ℝ) = 22 * (ell : ℝ) * B := by
    rw [hDcast]
    simpa only [B, Nat.cast_mul, Nat.cast_ofNat] using
      (log_pow ((m : ℝ) * (ell : ℝ) ^ 2) (22 * ell))
  have hv6 : v ≤ v ^ 6 := by
    simpa only [pow_one] using pow_le_pow_right₀ hv (by decide : 1 ≤ 6)
  have hCv : v ^ 6 ≤ C * v ^ 6 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (show 1 ≤ C by linarith) (pow_nonneg hv0 6)
  have hgEll : g * (ell : ℝ) ≤ (ell : ℝ) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hg1 hell0
  have hvEll : v ≤ (ell : ℝ) := hv6.trans (hCv.trans (hfirst.trans hgEll))
  have hEllB : (ell : ℝ) ≤ (ell : ℝ) * B := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hB hell0
  have hgapLog : 1 + log (1 / g) ≤ (ell : ℝ) * B := by
    have hgv : 1 + log (1 / g) ≤ v := by dsimp only [v]; linarith only [hlogm, hlogw]
    exact hgv.trans (hvEll.trans hEllB)
  obtain ⟨ht21, htPower, htUpper⟩ := interleaved_threshold_width_bounds
    Ctail g w ell B D s hCtail hg hg1 hw (by linarith) hB hD hs hcount hgapLog hsLog
  exact ⟨hw, hell, hD, hs, hB, hcount, ht21, htPower, htUpper⟩

/-- The two derived scale inequalities give the actual fourth-power
Chebyshev budget. This is scalar algebra supporting ALVV,
arXiv:1602.08828v2, lines 1010–1024 and 1797–1805. -/
private theorem interleaved_fourth_power_bound (T0 g e B w t P : ℝ)
    (hT0 : 0 ≤ T0) (hg : 0 ≤ g) (he : 0 ≤ e) (hB : 0 ≤ B) (hw : 0 ≤ w)
    (hP : 0 ≤ P) (hwidth : t ≤ T0 * (e * B + w)) (hdegree : P ≤ 72 * e * B)
    (hfirst : 100000 * T0 * B ^ 3 ≤ g * e)
    (hsecond : 100000 * T0 * w * B ^ 2 ≤ g * e ^ 2) :
    7 * t * P ^ 2 ≤ (4 * g / 5) * e ^ 4 := by
  have hPsq := pow_le_pow_left₀ hP hdegree 2
  have hproduct := mul_le_mul hwidth hPsq (sq_nonneg P) (by positivity)
  have hbound : 7 * t * P ^ 2 ≤ 36288 * T0 * (e ^ 3 * B ^ 3 + w * e ^ 2 * B ^ 2) := by
    calc
      _ = 7 * (t * P ^ 2) := by ring
      _ ≤ 7 * (T0 * (e * B + w) * (72 * e * B) ^ 2) :=
        mul_le_mul_of_nonneg_left hproduct (by norm_num)
      _ = _ := by ring
  have hfirstMul := mul_le_mul_of_nonneg_right hfirst (pow_nonneg he 3)
  have hsecondMul := mul_le_mul_of_nonneg_right hsecond (sq_nonneg e)
  have hsum : 100000 * T0 * (e ^ 3 * B ^ 3 + w * e ^ 2 * B ^ 2) ≤ 2 * g * e ^ 4 := by
    nlinarith only [hfirstMul, hsecondMul]
  nlinarith only [hbound, hsum, mul_nonneg hg (pow_nonneg he 4)]

/-- Logarithmic suppression of the squared Chebyshev envelope controls
its product with the actual natural count. Scalar auxiliary to ALVV,
arXiv:1602.08828v2, Theorem `t:ais`, lines 1010–1024. -/
private theorem chebyshev_squared_count_tradeoff (D : ℕ) (x : ℝ)
    (hD : 0 < (D : ℝ)) (hx : 3 * log (D : ℝ) + log 800000 / 4 ≤ x) :
    (D : ℝ) ^ 12 * (2 * exp (-2 * x)) ^ 2 ≤ 1 / 200000 := by
  have hproduct : 0 < (D : ℝ) ^ 12 * (2 * exp (-2 * x)) ^ 2 := by positivity
  apply (log_le_log_iff hproduct (by norm_num : (0 : ℝ) < 1 / 200000)).mp
  rw [log_mul (pow_ne_zero 12 hD.ne')
      (pow_ne_zero 2 (mul_ne_zero (by norm_num) (exp_ne_zero _))),
    log_pow, log_pow,
    log_mul (by norm_num : (2 : ℝ) ≠ 0) (exp_ne_zero _), log_exp,
    log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (200000 : ℝ) ≠ 0), log_one]
  have hconstant : log (800000 : ℝ) = 2 * log 2 + log 200000 := by
    calc
      log (800000 : ℝ) = log ((2 : ℝ) ^ 2 * 200000) := by norm_num
      _ = log ((2 : ℝ) ^ 2) + log 200000 := log_mul (by norm_num) (by norm_num)
      _ = _ := by rw [log_pow]; norm_num
  norm_num only [Nat.cast_ofNat]
  nlinarith only [hx, hconstant]

/-- The actual independent window, sample ceiling and tiny accuracy give
suppression at their same count, with a strict factor-two margin. The
only constant condition is discharged by uniform logarithmic absorption.
Supporting ALVV, arXiv:1602.08828v2, lines 1010–1024 and 1797–1805. -/
theorem interleaved_actual_filter_tradeoff
    (Ctail C : ℝ) (m r L : ℕ) (g : ℝ)
    (hCtail : 21 ≤ Ctail) (hC : 21 ≤ C)
    (habsorb : (100000 * (4000 * Ctail)) * (14 + 2 * log (C + 1)) ^ 3 ≤ C)
    (hm : 50 ≤ m) (hr : 1 ≤ r) (hg : 0 < g) (hg1 : g ≤ 1) :
    let w := 1 + log (r : ℝ) + 2 * log ((L : ℝ) + 1)
    let v := 1 + log (m : ℝ) + log (1 / g) + log (1 + w)
    let ell := Nat.ceil (C * (v ^ 6 / g + sqrt w * v ^ 3 / sqrt g))
    let D := (m * ell ^ 2) ^ (22 * ell)
    let A := log (D : ℝ) + w
    let s := Nat.ceil (4096 * (r : ℝ) * A)
    let a := 3 / (32 * (D : ℝ) ^ 12 * (s : ℝ) ^ 5)
    let tau := a ^ 2 / 1048576
    let t := Ctail * (1 + log (1 / g) + log (1 / tau))
    let Delta := (1 / 200000 : ℝ) / (D : ℝ) ^ 12
    (D : ℝ) ^ 12 * Delta < 1 / 100000 ∧
      ∀ R : ℝ, 0 < R → R ≤ 3 * t + 4 * (ell : ℝ) →
        (2 * exp (-2 * (ell : ℝ) ^ 2 * sqrt ((4 * g / 5) / R))) ^ 2 ≤ Delta := by
  intro w v ell D A s a tau t Delta
  let B := log ((m : ℝ) * (ell : ℝ) ^ 2)
  let T0 := 4000 * Ctail
  let P := 3 * log (D : ℝ) + log 800000 / 4
  obtain ⟨hw, hell, hD, hs, hB, hcount, ht21, htPower, htWidth⟩ :=
    interleaved_actual_threshold_width_bounds Ctail C m r L g hCtail hC hm hr hg hg1
  change 21 ≤ ell at hell
  change 2 ≤ D at hD
  change 1 ≤ s at hs
  change 1 ≤ B at hB
  change log (D : ℝ) = 22 * (ell : ℝ) * B at hcount
  change P ≤ t at htPower
  change t ≤ T0 * ((ell : ℝ) * B + w) at htWidth
  have hE0 : 0 ≤ (ell : ℝ) := Nat.cast_nonneg _
  have hE1 : (1 : ℝ) ≤ ell := by exact_mod_cast (show 1 ≤ ell by omega)
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hlogD : 0 ≤ log (D : ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ D by omega))
  have hP0 : 0 ≤ P := by
    have hlogMargin : 0 ≤ log (800000 : ℝ) := log_nonneg (by norm_num)
    dsimp only [P]
    positivity
  have hEB : 1 ≤ (ell : ℝ) * B := one_le_mul_of_one_le_of_one_le hE1 hB
  have hdegree : P ≤ 72 * (ell : ℝ) * B := by
    dsimp only [P]
    nlinarith only [hcount, hEB, log_filter_margin_le]
  have hK : 1 ≤ 100000 * T0 := by dsimp only [T0]; linarith only [hCtail]
  obtain ⟨hfirst, hsecond⟩ := interleaved_filter_scale_dominates_width
    (100000 * T0) C m g w hK hC habsorb hm hg hg1 hw
  change 100000 * T0 * B ^ 3 ≤ g * (ell : ℝ) at hfirst
  change 100000 * T0 * w * B ^ 2 ≤ g * (ell : ℝ) ^ 2 at hsecond
  have hT0 : 0 ≤ T0 := by dsimp only [T0]; linarith only [hCtail]
  have hfourth := interleaved_fourth_power_bound T0 g ell B w t P
    hT0 hg.le hE0 (by linarith) (by linarith) hP0 htWidth hdegree hfirst hsecond
  have hlow : 100000 * T0 ≤ 100000 * T0 * B ^ 3 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (one_le_pow₀ hB : 1 ≤ B ^ 3) (by positivity)
  have hscale21 : 21 ≤ g * (ell : ℝ) := by
    have hK21 : 21 ≤ 100000 * T0 := by dsimp only [T0]; linarith only [hCtail]
    exact hK21.trans (hlow.trans hfirst)
  have hbase : 7 ≤ (ell : ℝ) * (4 * g / 5) := by nlinarith only [hscale21]
  have hDeltaEq : (D : ℝ) ^ 12 * Delta = 1 / 200000 := by
    dsimp only [Delta]
    field_simp [hD0.ne']
  constructor
  · rw [hDeltaEq]
    norm_num
  · intro R hR hRwidth
    have hexponent := independent_truncation_filter_exponent (ell : ℝ) t (4 * g / 5) P R
      hE0 hP0 htPower hbase hfourth hR hRwidth
    have hproduct := chebyshev_squared_count_tradeoff D
      ((ell : ℝ) ^ 2 * sqrt ((4 * g / 5) / R)) hD0 hexponent
    apply (le_div_iff₀ (pow_pos hD0 12)).mpr
    calc
      _ = (D : ℝ) ^ 12 *
          (2 * exp (-2 * (ell : ℝ) ^ 2 * sqrt ((4 * g / 5) / R))) ^ 2 := mul_comm _ _
      _ ≤ _ := by
        have harg := (mul_assoc (-2 : ℝ) ((ell : ℝ) ^ 2)
          (sqrt ((4 * g / 5) / R))).symm
        simpa only [harg] using hproduct

/-- Universal constants construct the actual independent window, count,
sample size, tiny alignment accuracy and clipping threshold. Both the
physical tail and the filter suppression are derived at that same count.
The scale uses the fixed failure target `(L+1)^(-2)`, before child spaces;
no uniformity over arbitrarily small failure parameters is claimed.
Supporting ALVV, arXiv:1602.08828v2, lines 1010–1024 and 1797–1805. -/
theorem exists_interleaved_physical_scalar_parameters :
    ∃ Ctail C : ℝ, 21 ≤ Ctail ∧ 21 ≤ C ∧
      ∀ (m r L : ℕ) (g : ℝ), 50 ≤ m → 1 ≤ r → 0 < g → g ≤ 1 →
      let w := 1 + log (r : ℝ) + 2 * log ((L : ℝ) + 1)
      let v := 1 + log (m : ℝ) + log (1 / g) + log (1 + w)
      let ell := Nat.ceil (C * (v ^ 6 / g + sqrt w * v ^ 3 / sqrt g))
      let D := (m * ell ^ 2) ^ (22 * ell)
      let A := log (D : ℝ) + w
      let s := Nat.ceil (4096 * (r : ℝ) * A)
      let a := 3 / (32 * (D : ℝ) ^ 12 * (s : ℝ) ^ 5)
      let tau := a ^ 2 / 1048576
      let epsilon := 200 * tau
      let t := Ctail * (1 + log (1 / g) + log (1 / tau))
      let Delta := (1 / 200000 : ℝ) / (D : ℝ) ^ 12
      21 ≤ ell ∧ 2 ≤ D ∧ 1 ≤ s ∧ 0 < a ∧ a ≤ 1 / 100 ∧
        0 < tau ∧ tau ≤ 1 ∧ 0 < epsilon ∧ epsilon ≤ 1 ∧ 21 ≤ t ∧
        (288 * exp (11 / 8)) * exp (-(t - g) / 8) ≤ epsilon * g / 1000000 ∧
        (D : ℝ) ^ 12 * Delta < 1 / 100000 ∧
        log (D : ℝ) ≤ 22 * (C + 1) * (14 + 2 * log (C + 1)) *
          (v ^ 7 / g + sqrt w * v ^ 4 / sqrt g) ∧
        ∀ R : ℝ, 0 < R → R ≤ 3 * t + 4 * (ell : ℝ) →
          (2 * exp (-2 * (ell : ℝ) ^ 2 * sqrt ((4 * g / 5) / R))) ^ 2 ≤ Delta := by
  obtain ⟨Ctail, hCtail, hthreshold⟩ := exists_independent_truncation_threshold_constant
  have hK : 0 < 100000 * (4000 * Ctail) := by linarith only [hCtail]
  obtain ⟨C, hC, _hM, habsorb⟩ :=
    exists_interleaved_log_absorption_constant (100000 * (4000 * Ctail)) 21 hK
  refine ⟨Ctail, C, hCtail, hC, ?_⟩
  intro m r L g hm hr hg hg1 w v ell D A s a tau epsilon t Delta
  obtain ⟨hw, hell, hD, hs, _hB, _hcount, ht21, _htPower, _htWidth⟩ :=
    interleaved_actual_threshold_width_bounds Ctail C m r L g hCtail hC hm hr hg hg1
  change 21 ≤ ell at hell
  change 2 ≤ D at hD
  change 1 ≤ s at hs
  obtain ⟨ha, ha1, htau, htau1, hepsilon1, _hreference⟩ :=
    interleaved_overlap_accuracy_bounds D s hD hs
  change 0 < tau at htau
  change tau ≤ 1 at htau1
  change epsilon ≤ 1 at hepsilon1
  obtain ⟨_ht, htail⟩ := hthreshold g tau hg hg1 htau htau1
  have htauEpsilon : tau ≤ epsilon := by dsimp only [epsilon]; linarith only [htau]
  have htailEpsilon : (288 * exp (11 / 8)) * exp (-(t - g) / 8) ≤
      epsilon * g / 1000000 :=
    htail.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right htauEpsilon hg.le) (by norm_num))
  obtain ⟨htradeoff, hfilter⟩ := interleaved_actual_filter_tradeoff
    Ctail C m r L g hCtail hC habsorb hm hr hg hg1
  obtain ⟨_hell, _hfirst, _hsecond, _hupper, _hbase, hlogD⟩ :=
    interleaved_filter_scale_count_bounds C m g w hC hm hg hg1 hw
  exact ⟨hell, hD, hs, ha, ha1, htau, htau1,
    mul_pos (by norm_num : (0 : ℝ) < 200) htau, hepsilon1,
    ht21, htailEpsilon, htradeoff, hlogD, hfilter⟩

end Real

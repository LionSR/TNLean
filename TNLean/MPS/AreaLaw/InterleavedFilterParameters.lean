/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.LogPowerAbsorption
import TNLean.MPS.AreaLaw.IndependentTruncationParameters

/-!
# Independent scales for interleaved physical filters

The clipping threshold and polynomial degree must be chosen independently
when the original-to-clipped error is tied to a very small sampling
overlap. These scalar estimates support ALVV, arXiv:1602.08828v2,
Figure `fig:merge-prime`, lines 1668–1670, and the parameter selection,
lines 1797–1805. No physical operator or successful sample is assumed to
have been constructed by a scalar statement.
-/

namespace Real

/-- The logarithmic constant can be chosen uniformly before the local
dimension, gap, chain length and sampling size. This is an auxiliary
constant selection for ALVV, arXiv:1602.08828v2, lines 1797–1805. -/
theorem exists_interleaved_log_absorption_constant (K M : ℝ) (hK : 0 < K) :
    ∃ C : ℝ, 21 ≤ C ∧ M ≤ C ∧ K * (14 + 2 * log (C + 1)) ^ 3 ≤ C := by
  obtain ⟨C, _hC, hCM, habsorb⟩ :=
    exists_log_cube_absorption_constant 14 2 K (max 21 M)
      (by norm_num) (by norm_num) hK
  exact ⟨C, (le_max_left 21 M).trans hCM, (le_max_right 21 M).trans hCM, habsorb⟩

/-- A window with the independent-scale ceiling bound has a logarithmic
count-base estimate retaining the extra logarithmic chain-size scale.
This is a scalar auxiliary for ALVV, arXiv:1602.08828v2,
Theorem `t:ais`, lines 1010–1024, and lines 1797–1805. -/
theorem interleaved_log_polynomial_base_le (C m g w v e : ℝ)
    (hC : 1 ≤ C) (hm : 2 ≤ m) (hg : 0 < g) (hg1 : g ≤ 1) (hw : 1 ≤ w)
    (hv : v = 1 + log m + log (1 / g) + log (1 + w))
    (he : 1 ≤ e) (heup : e ≤ (C + 1) * (1 + w) * v ^ 6 / g) :
    log (m * e ^ 2) ≤ (14 + 2 * log (C + 1)) * v := by
  have hm0 : 0 < m := by linarith
  have he0 : 0 < e := by linarith
  have hCp : 0 < C + 1 := by linarith
  have hwp : 0 < 1 + w := by linarith
  have hlogm : 0 ≤ log m := log_nonneg (by linarith)
  have hlogg : 0 ≤ log (1 / g) := log_nonneg ((one_le_div hg).mpr hg1)
  have hlogw : 0 ≤ log (1 + w) := log_nonneg (by linarith)
  have hv1 : 1 ≤ v := by rw [hv]; linarith
  have hv0 : 0 < v := by linarith
  have hlogC : 0 ≤ log (C + 1) := log_nonneg (by linarith)
  have hloge : log e ≤ log (C + 1) + log (1 + w) + 6 * log v + log (1 / g) := by
    calc
      log e ≤ log ((C + 1) * (1 + w) * v ^ 6 / g) := log_le_log he0 heup
      _ = _ := by
        rw [log_div (by positivity) hg.ne',
          log_mul (by positivity) (pow_ne_zero 6 hv0.ne'),
          log_mul hCp.ne' hwp.ne', log_pow, one_div, log_inv]
        ring
  have hlogv : log v ≤ v := log_le_self hv0.le
  have hsum : log m + 2 * log (1 / g) + 2 * log (1 + w) ≤ 2 * v := by
    rw [hv]
    linarith
  have hlogCv : log (C + 1) ≤ log (C + 1) * v := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hv1 hlogC
  calc
    log (m * e ^ 2) = log m + 2 * log e := by
      rw [log_mul hm0.ne' (pow_ne_zero 2 he0.ne'), log_pow]
      norm_num
    _ ≤ 2 * log (C + 1) + 14 * v := by linarith
    _ ≤ (14 + 2 * log (C + 1)) * v := by nlinarith

/-- The logarithmic scale is at least one in the physical parameter range.
Scalar auxiliary for ALVV, arXiv:1602.08828v2, lines 1797–1805. -/
theorem one_le_interleaved_log_scale (m g w : ℝ)
    (hm : 2 ≤ m) (hg : 0 < g) (hg1 : g ≤ 1) (hw : 1 ≤ w) :
    1 ≤ 1 + log m + log (1 / g) + log (1 + w) := by
  have hmLog : 0 ≤ log m := log_nonneg (by linarith)
  have hgLog : 0 ≤ log (1 / g) := log_nonneg ((one_le_div hg).mpr hg1)
  have hwLog : 0 ≤ log (1 + w) := log_nonneg (by linarith)
  linarith

/-- The two positive contributions to the independent window control both
its ceiling and the truncation-dominated regime. Scalar auxiliary for
ALVV, arXiv:1602.08828v2, lines 1797–1805. -/
private theorem interleaved_filter_ceil_bounds (C g w v : ℝ)
    (hC : 21 ≤ C) (hg : 0 < g) (hg1 : g ≤ 1) (hw : 1 ≤ w) (hv : 1 ≤ v) :
    let ell := Nat.ceil (C * (v ^ 6 / g + sqrt w * v ^ 3 / sqrt g))
    21 ≤ ell ∧ C * v ^ 6 ≤ g * (ell : ℝ) ∧
      C * sqrt w * v ^ 3 ≤ sqrt g * (ell : ℝ) ∧
      (ell : ℝ) ≤ (C + 1) * (v ^ 6 / g + sqrt w * v ^ 3 / sqrt g) ∧
      (ell : ℝ) ≤ (C + 1) * (1 + w) * v ^ 6 / g := by
  intro ell
  have hC0 : 0 ≤ C := by linarith
  have hv0 : 0 < v := by linarith
  have hrootg : 0 < sqrt g := sqrt_pos.mpr hg
  have hrootw : 0 ≤ sqrt w := sqrt_nonneg _
  have hv6 : 1 ≤ v ^ 6 := one_le_pow₀ hv
  have hv36 : v ^ 3 ≤ v ^ 6 := pow_le_pow_right₀ hv (by decide : 3 ≤ 6)
  have hwroot : sqrt w ≤ w := sqrt_le_self_iff.mpr (Or.inr hw)
  have hgroot : g ≤ sqrt g := (le_sqrt hg.le hg.le).mpr (by nlinarith)
  have hratio : 1 ≤ v ^ 6 / g := (le_div_iff₀ hg).mpr (by nlinarith)
  let X := v ^ 6 / g + sqrt w * v ^ 3 / sqrt g
  have hother : 0 ≤ sqrt w * v ^ 3 / sqrt g := by positivity
  have hX : 1 ≤ X := by
    dsimp only [X]
    linarith only [hratio, hother]
  have hX0 : 0 ≤ X := by linarith
  have hlower : C * X ≤ (ell : ℝ) := Nat.le_ceil _
  have hupper : (ell : ℝ) ≤ C * X + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hC0 hX0)).le
  have hfirst : C * v ^ 6 / g ≤ (ell : ℝ) := by
    calc
      _ = C * (v ^ 6 / g) := by ring
      _ ≤ C * X := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hother) hC0
      _ ≤ _ := hlower
  have hsecond : C * sqrt w * v ^ 3 / sqrt g ≤ (ell : ℝ) := by
    calc
      _ = C * (sqrt w * v ^ 3 / sqrt g) := by ring
      _ ≤ C * X := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) hC0
      _ ≤ _ := hlower
  have hCX : C ≤ C * X := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hX hC0
  have hellC : C ≤ (ell : ℝ) := hCX.trans hlower
  have hell : 21 ≤ ell := by exact_mod_cast hC.trans hellC
  have hfirst' : C * v ^ 6 ≤ g * (ell : ℝ) := by
    have h := (div_le_iff₀ hg).mp hfirst
    nlinarith only [h]
  have hsecond' : C * sqrt w * v ^ 3 ≤ sqrt g * (ell : ℝ) := by
    have h := (div_le_iff₀ hrootg).mp hsecond
    nlinarith only [h]
  have hcoarseX : X ≤ (1 + w) * v ^ 6 / g := by
    have hterm : sqrt w * v ^ 3 / sqrt g ≤ w * v ^ 6 / g := by
      calc
        _ ≤ w * v ^ 6 / sqrt g := div_le_div_of_nonneg_right
          (mul_le_mul hwroot hv36 (by positivity) (by linarith)) hrootg.le
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hg hgroot
    dsimp only [X]
    calc
      _ ≤ v ^ 6 / g + w * v ^ 6 / g := by linarith only [hterm]
      _ = _ := by ring
  have hrefined : (ell : ℝ) ≤ (C + 1) * X := by nlinarith
  refine ⟨hell, hfirst', hsecond', hrefined, ?_⟩
  calc
    _ ≤ (C + 1) * X := hrefined
    _ ≤ (C + 1) * ((1 + w) * v ^ 6 / g) :=
      mul_le_mul_of_nonneg_left hcoarseX (by linarith)
    _ = _ := by ring

/-- The actual independent ceiling has a logarithmic count bound with a
square-root dependence on the logarithmic size scale, up to explicit
logarithmic factors. The constant precedes all physical data.
Supporting ALVV, arXiv:1602.08828v2, Theorem `t:ais`, lines 1010–1024,
and the interleaved parameter selection, lines 1797–1805. -/
theorem interleaved_filter_scale_count_bounds (C : ℝ) (m : ℕ) (g w : ℝ)
    (hC : 21 ≤ C) (hm : 50 ≤ m) (hg : 0 < g) (hg1 : g ≤ 1) (hw : 1 ≤ w) :
    let v := 1 + log (m : ℝ) + log (1 / g) + log (1 + w)
    let ell := Nat.ceil (C * (v ^ 6 / g + sqrt w * v ^ 3 / sqrt g))
    let D := (m * ell ^ 2) ^ (22 * ell)
    let J := 14 + 2 * log (C + 1)
    21 ≤ ell ∧ C * v ^ 6 ≤ g * (ell : ℝ) ∧
      C * sqrt w * v ^ 3 ≤ sqrt g * (ell : ℝ) ∧
      (ell : ℝ) ≤ (C + 1) * (v ^ 6 / g + sqrt w * v ^ 3 / sqrt g) ∧
      log ((m : ℝ) * (ell : ℝ) ^ 2) ≤ J * v ∧
      log (D : ℝ) ≤ 22 * (C + 1) * J *
        (v ^ 7 / g + sqrt w * v ^ 4 / sqrt g) := by
  intro v ell D J
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
  have hv : 1 ≤ v := one_le_interleaved_log_scale m g w hmR hg hg1 hw
  obtain ⟨hell, hfirst, hsecond, hupper, hcoarse⟩ :=
    interleaved_filter_ceil_bounds C g w v hC hg hg1 hw hv
  have hbase := interleaved_log_polynomial_base_le C m g w v ell
    (by linarith) hmR hg hg1 hw rfl (by exact_mod_cast (show 1 ≤ ell by omega)) hcoarse
  have hJ : 0 ≤ J := by
    have hlog : 0 ≤ log (C + 1) := log_nonneg (by linarith)
    dsimp only [J]
    linarith
  have hell0 : 0 ≤ (ell : ℝ) := Nat.cast_nonneg _
  have hlogD : log (D : ℝ) ≤ 22 * (ell : ℝ) * J * v := by
    have hm0 : (0 : ℝ) < m := by linarith
    have hellpos : (0 : ℝ) < ell := by exact_mod_cast (show 0 < ell by omega)
    dsimp only [D]
    push_cast
    rw [log_pow]
    push_cast
    nlinarith only [mul_le_mul_of_nonneg_left hbase
      (show 0 ≤ 22 * (ell : ℝ) by positivity)]
  have hAlgebra (x j : ℝ) :
      22 * ((C + 1) * (x ^ 6 / g + sqrt w * x ^ 3 / sqrt g)) * j * x =
        22 * (C + 1) * j * (x ^ 7 / g + sqrt w * x ^ 4 / sqrt g) := by ring
  have hAC (x : ℝ) : 22 * x * J * v = x * (22 * J * v) := by ac_rfl
  refine ⟨hell, hfirst, hsecond, hupper, hbase, ?_⟩
  calc
    _ ≤ 22 * (ell : ℝ) * J * v := hlogD
    _ = (ell : ℝ) * (22 * J * v) := hAC _
    _ ≤ ((C + 1) * (v ^ 6 / g + sqrt w * v ^ 3 / sqrt g)) * (22 * J * v) :=
      mul_le_mul_of_nonneg_right hupper (show 0 ≤ 22 * J * v by positivity)
    _ = 22 * ((C + 1) * (v ^ 6 / g + sqrt w * v ^ 3 / sqrt g)) * J * v := (hAC _).symm
    _ = _ := hAlgebra v J

/-- The explicitly constructed independent window dominates both terms
in the actual fourth-power suppression condition. No window or count is
supplied as a witness. This is a scalar auxiliary for ALVV,
arXiv:1602.08828v2, Theorem `t:ais`, lines 1010–1024,
and the interleaved parameter selection, lines 1797–1805. -/
theorem interleaved_filter_scale_dominates_width
    (K C : ℝ) (m : ℕ) (g w : ℝ) (hK : 1 ≤ K) (hC : 21 ≤ C)
    (habsorb : K * (14 + 2 * log (C + 1)) ^ 3 ≤ C)
    (hm : 50 ≤ m) (hg : 0 < g) (hg1 : g ≤ 1) (hw : 1 ≤ w) :
    let v := 1 + log (m : ℝ) + log (1 / g) + log (1 + w)
    let ell := Nat.ceil (C * (v ^ 6 / g + sqrt w * v ^ 3 / sqrt g))
    let B := log ((m : ℝ) * (ell : ℝ) ^ 2)
    K * B ^ 3 ≤ g * (ell : ℝ) ∧ K * w * B ^ 2 ≤ g * (ell : ℝ) ^ 2 := by
  intro v ell B
  let J := 14 + 2 * log (C + 1)
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
  have hv : 1 ≤ v := one_le_interleaved_log_scale m g w hmR hg hg1 hw
  have hv0 : 0 ≤ v := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hJ : 1 ≤ J := by
    have hlog : 0 ≤ log (C + 1) := log_nonneg (by linarith)
    dsimp only [J]
    linarith
  obtain ⟨hell, hfirst, hsecond, _hupper, hbase, _hlogD⟩ :=
    interleaved_filter_scale_count_bounds C m g w hC hm hg hg1 hw
  change 21 ≤ ell at hell
  have hBNat : 1 ≤ m * ell ^ 2 := by
    simpa only [one_mul] using Nat.mul_le_mul (show 1 ≤ m by omega)
      (Nat.one_le_pow 2 ell (by omega))
  have hB0 : 0 ≤ B := log_nonneg (by exact_mod_cast hBNat)
  have hC2 : K * J ^ 2 ≤ C ^ 2 := by
    have hJ23 : J ^ 2 ≤ J ^ 3 := pow_le_pow_right₀ hJ (by decide : 2 ≤ 3)
    have hC12 : C ≤ C ^ 2 := by nlinarith
    exact (mul_le_mul_of_nonneg_left hJ23 hK0).trans (habsorb.trans hC12)
  have hsecondSq : C ^ 2 * w * v ^ 6 ≤ g * (ell : ℝ) ^ 2 := by
    have hsquare := pow_le_pow_left₀
      (by positivity : 0 ≤ C * sqrt w * v ^ 3) hsecond 2
    simpa only [mul_pow, sq_sqrt (show 0 ≤ w by linarith), sq_sqrt hg.le,
      ← pow_mul, show (3 : ℕ) * 2 = 6 by decide] using hsquare
  constructor
  · calc
      _ ≤ K * (J * v) ^ 3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hB0 hbase 3) hK0
      _ = K * J ^ 3 * v ^ 3 := by rw [mul_pow, ← mul_assoc]
      _ ≤ C * v ^ 3 := mul_le_mul_of_nonneg_right habsorb (pow_nonneg hv0 3)
      _ ≤ C * v ^ 6 := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hv (by decide : 3 ≤ 6)) hC0
      _ ≤ _ := hfirst
  · calc
      _ ≤ K * w * (J * v) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hB0 hbase 2) (by positivity)
      _ = (K * J ^ 2) * w * v ^ 2 := by rw [mul_pow]; ac_rfl
      _ ≤ C ^ 2 * w * v ^ 2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC2 (by linarith)) (sq_nonneg v)
      _ ≤ C ^ 2 * w * v ^ 6 := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hv (by decide : 2 ≤ 6)) (by positivity)
      _ ≤ _ := hsecondSq

end Real

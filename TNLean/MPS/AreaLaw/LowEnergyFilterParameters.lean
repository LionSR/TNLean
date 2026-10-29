/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PolynomialFilterParameters

/-!
# Interior low-energy filter parameters

At fixed low-density bandwidth, one scalar choice controls the actual
physical truncation threshold and polynomial family. The exact logarithmic
bound retains the capped width `g = min w 1`. These estimates support ALVV,
arXiv:1602.08828v2, Theorem `t:aisgapless`, lines 1027–1041.
-/

namespace Real

/-- The prescribed physical threshold is bounded uniformly over smaller
bandwidths. Auxiliary to ALVV, arXiv:1602.08828v2, Theorem `t:aisgapless`,
lines 1027–1041. The comparison error is fixed at `1/200`. -/
theorem low_energy_threshold_le
    (etaLD eta w : ℝ) (hLD : 0 < etaLD) (heta : 0 ≤ eta)
    (hetaup : eta ≤ etaLD) (hw : 0 < w) :
    let g := min w 1
    let C := 288 * exp (11 / 8)
    let T := 21 + etaLD + 8 * log (400 * C * (6 + etaLD))
    21 + eta + 8 * log (C / min 1 ((1 / 200 : ℝ) * w ^ 2 / (2 * (6 + eta)))) ≤
      T + 16 * log (1 / g) := by
  intro g C T
  have hg : 0 < g := lt_min hw zero_lt_one
  have hg1 : g ≤ 1 := min_le_right _ _
  have hgw : g ≤ w := min_le_left _ _
  have hC : 0 < C := by positivity
  let z := g ^ 2 / (400 * (6 + etaLD))
  have hz : 0 < z := by dsimp only [z]; positivity
  have hz1 : z ≤ 1 := by
    dsimp only [z]
    apply (div_le_iff₀ (by positivity : 0 < 400 * (6 + etaLD))).mpr
    nlinarith only [sq_nonneg (1 - g), mul_nonneg hg.le (sub_nonneg.mpr hg1), hLD]
  have hzw : z ≤ (1 / 200 : ℝ) * w ^ 2 / (2 * (6 + eta)) := by
    calc
      z ≤ w ^ 2 / (400 * (6 + etaLD)) := by dsimp only [z]; gcongr
      _ ≤ w ^ 2 / (400 * (6 + eta)) := by gcongr
      _ = (1 / 200 : ℝ) * w ^ 2 / (2 * (6 + eta)) := by
        field_simp
        ring
  have hzmin := le_min hz1 hzw
  have hmin : 0 < min 1 ((1 / 200 : ℝ) * w ^ 2 / (2 * (6 + eta))) :=
    hz.trans_le hzmin
  have hlog := log_le_log (div_pos hC hmin)
    (div_le_div_of_nonneg_left hC.le hz hzmin)
  calc
    _ ≤ 21 + etaLD + 8 * log (C / z) := by linarith only [hetaup, hlog]
    _ = T + 16 * log (1 / g) := by
      have heq : C / z = (400 * C * (6 + etaLD)) * (1 / g) ^ 2 := by
        dsimp only [z]
        field_simp
      rw [heq, log_mul (by positivity : 400 * C * (6 + etaLD) ≠ 0)
        (pow_ne_zero 2 (one_div_ne_zero hg.ne')), log_pow]
      dsimp only [T]
      ring


/-- At fixed density bandwidth, one constant controls the square-degree
filter for every smaller physical bandwidth. The prescribed threshold and
its physical lower bound precede this scalar estimate. The exact count
retains the capped width. ALVV, arXiv:1602.08828v2, Theorem
`t:aisgapless`, lines 1027–1041. -/
theorem exists_low_energy_scalar_parameters (etaLD : ℝ) (hLD : 0 < etaLD) :
    let T := 21 + etaLD + 8 * log (400 * (288 * exp (11 / 8)) * (6 + etaLD))
    let CH := (3 * T + 52) / 2
    ∃ A : ℝ, 1 ≤ A ∧ 21 ≤ A ∧
      ∀ (q : ℕ) (eta w E0 t : ℝ), 2 ≤ q → 0 < w → 3 * w < eta → eta ≤ etaLD →
      t = 21 + eta + 8 * log ((288 * exp (11 / 8)) /
        min 1 ((1 / 200 : ℝ) * w ^ 2 / (2 * (6 + eta)))) →
      19 + eta ≤ t → 0 ≤ E0 → E0 ≤ 4 →
      let g := min w 1
      let u := 1 + log (q : ℝ) + log (1 / g)
      let ell : ℕ := ⌈A * u ^ 2 / g⌉₊
      let D := (q * ell ^ 2) ^ (18 * ell + 2 * (ell ^ 2 / ell))
      let R := 3 * t + 4 * (ell : ℝ) - (E0 + eta - 2 * w)
      let Delta := (2 * exp (-2 * ((ell ^ 2 : ℕ) : ℝ) * sqrt (w / R))) ^ 2
      21 ≤ ell ∧ 0 < R ∧ R ≤ 2 * CH * (ell : ℝ) ∧ 0 < Delta ∧
      log (D : ℝ) ≤ 22 * (A + 1) * (6 + 2 * log (A + 1)) / g * u ^ 3 ∧
      (D : ℝ) ^ 12 * Delta < 1 / 100000 := by
  intro T CH
  have hT : 0 < T := by
    have hC : 1 ≤ 288 * exp (11 / 8) := by
      have he := one_le_exp_iff.mpr (show (0 : ℝ) ≤ 11 / 8 by norm_num)
      linarith only [he]
    have hlog : 0 ≤ log (400 * (288 * exp (11 / 8)) * (6 + etaLD)) :=
      log_nonneg (by nlinarith only [hC, hLD])
    dsimp only [T]
    linarith only [hLD, hlog]
  obtain ⟨A, hA, hA21, _hAM, _hAlog, hall⟩ :=
    exists_dg_scalar_parameters CH 0 (by dsimp only [CH]; positivity)
  refine ⟨A, hA, hA21, ?_⟩
  intro q eta w E0 t hq hw hbuffer heta ht hcut hE0 hE04 g u ell D R Delta
  have hg : 0 < g := lt_min hw zero_lt_one
  have hg1 : g ≤ 1 := min_le_right _ _
  have hgw : g ≤ w := min_le_left _ _
  obtain ⟨hellLower, _hellUpper, hellA, _hcount, hlogD, htrade, _htail⟩ :=
    hall q g hq hg hg1
  have hellR : (21 : ℝ) ≤ (ell : ℝ) := hA21.trans hellA
  have hell : 21 ≤ ell := by exact_mod_cast hellR
  have hb : 0 ≤ log (1 / g) := log_nonneg ((one_le_div hg).mpr hg1)
  have hlogq : 0 ≤ log (q : ℝ) :=
    log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
  have hu : 1 + log (1 / g) ≤ u := by dsimp only [u]; linarith only [hlogq]
  have hellb : log (1 / g) ≤ (ell : ℝ) := by
    calc
      log (1 / g) ≤ u ^ 2 := by nlinarith only [hu, hb, sq_nonneg (u - 1)]
      _ ≤ A * u ^ 2 / g := (le_div_iff₀ hg).mpr
        (by nlinarith only [mul_le_mul_of_nonneg_right (hg1.trans hA) (sq_nonneg u)])
      _ ≤ (ell : ℝ) := hellLower
  have hR : 0 < R := by
    dsimp only [R]
    linarith only [hcut, hw, hbuffer, hE04, hellR]
  have htup : t ≤ T + 16 * log (1 / g) := by
    rw [ht]
    exact low_energy_threshold_le etaLD eta w hLD
      (by linarith only [hw, hbuffer]) heta hw
  have hRup : R ≤ 2 * CH * (ell : ℝ) := by
    have hmul := mul_nonneg hT.le (show 0 ≤ (ell : ℝ) - 1 by linarith only [hellR])
    dsimp only [CH, R]
    nlinarith only [htup, hellb, hmul, hE0, hbuffer, hw]
  have hDelta : 0 < Delta := by dsimp only [Delta]; positivity
  let Daux := (q * ell ^ 2) ^ (22 * ell)
  have hdiv : ell ^ 2 / ell = ell := by
    rw [pow_two, Nat.mul_div_cancel ell (by omega : 0 < ell)]
  have hbase : 1 < q * ell ^ 2 := by
    have hsq : 1 ≤ ell ^ 2 := one_le_pow₀ (show 1 ≤ ell by omega)
    nlinarith only [Nat.mul_le_mul_left q hsq, hq]
  have hDlt : D < Daux := by
    dsimp only [D, Daux]
    rw [hdiv]
    apply pow_lt_pow_right₀ hbase
    omega
  have hDpos : 0 < (D : ℝ) := by
    exact_mod_cast (show 0 < D from Nat.pow_pos (by omega : 0 < q * ell ^ 2))
  have hDcastlt : (D : ℝ) < (Daux : ℝ) := by exact_mod_cast hDlt
  refine ⟨hell, hR, hRup, hDelta,
    (log_le_log hDpos hDcastlt.le).trans hlogD, ?_⟩
  have hDelEq : Delta = 4 * exp (-4 * (ell : ℝ) ^ 2 * sqrt (w / R)) := by
    dsimp only [Delta]
    rw [mul_pow, ← exp_nat_mul, Nat.cast_pow, show (2 : ℝ) ^ 2 = 4 by norm_num]
    change 4 * exp (2 * (-2 * (ell : ℝ) ^ 2 * sqrt (w / R))) = _
    congr 1
    congr 1
    ring
  have hsqrt : sqrt ((4 * g / 5) / R) ≤ sqrt (w / R) :=
    sqrt_le_sqrt (div_le_div_of_nonneg_right (by linarith only [hgw, hg]) hR.le)
  have hDelLe : Delta ≤ 4 * exp (-(4 * (ell : ℝ) ^ 2 * sqrt ((4 * g / 5) / R))) := by
    rw [hDelEq]
    exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr
      (by nlinarith only [mul_le_mul_of_nonneg_left hsqrt (sq_nonneg (ell : ℝ))]))
      (by norm_num)
  have hpowlt : (D : ℝ) ^ 12 < (Daux : ℝ) ^ 12 := by gcongr
  calc
    (D : ℝ) ^ 12 * Delta < (Daux : ℝ) ^ 12 * Delta :=
      mul_lt_mul_of_pos_right hpowlt hDelta
    _ ≤ (Daux : ℝ) ^ 12 *
        (4 * exp (-(4 * (ell : ℝ) ^ 2 * sqrt ((4 * g / 5) / R)))) :=
      mul_le_mul_of_nonneg_left hDelLe (by positivity)
    _ ≤ 1 / 100000 := htrade R hR hRup

end Real

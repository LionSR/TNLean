/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.EfficientSoftLowDensityWindows
import TNLean.MPS.AreaLaw.SoftTruncationMPOAccuracy
import QICLean.Analysis.Parameter.SoftFamilyCalibration
import QICLean.Analysis.Real.GeometricOrderPolynomialBound

/-!
# Scalar budgets for the calibrated efficient low-density family

Elementary inequalities that turn the explicit losses of the efficient soft low-density
family into fixed thresholds: a residual bound at the floor `156 + 2 g` controls every
residual scale with a smaller floor, a window resolution `h = w² / (1000 (8 η + 24))` makes
the windowed loss at most `1 / 1000`, a precision `ξ ≤ w⁴ / (80000 (M + 8))` makes the
perturbation loss at most `1 / 1000`, and the contraction at the calibrated gap `w² / 2`
dominates the contraction between the two windows. Numerical auxiliaries to ALVV,
arXiv:1602.08828v2, `t:aisgaplessefficient`, lines 1424–1437.
-/

namespace TNLean.MPS.AreaLaw.ALVV

/-- A residual bound at the floor `V₀` controls the residual at every smaller floor `V` with at
most four crossing terms. Numerical auxiliary to ALVV, arXiv:1602.08828v2,
`t:aisgaplessefficient`, lines 1446–1457. -/
theorem soft_residual_le_of_floor_le {C V V0 T R B : ℝ} (hC4 : C ≤ 4)
    (hV : V ≤ V0) (hB : 3 * (32 * Real.exp (-(T - V0) / 8) + R) ≤ B) :
    3 * ((8 * C) * Real.exp (-(T - V) / 8) + R) ≤ B := by
  have he : Real.exp (-(T - V) / 8) ≤ Real.exp (-(T - V0) / 8) :=
    Real.exp_le_exp.mpr (by linarith)
  have hpos := Real.exp_pos (-(T - V) / 8)
  have : (8 * C) * Real.exp (-(T - V) / 8) ≤ 32 * Real.exp (-(T - V0) / 8) := by nlinarith
  linarith

/-- With the window resolution `h = w² / (1000 (8 η + 24))` and a residual scale `ρ ≤ h`, the
windowed loss at any band width `0 ≤ η' ≤ η` is at most `1 / 1000`. Numerical auxiliary to
ALVV, arXiv:1602.08828v2, `t:aisgaplessefficient`, lines 1446–1457. -/
theorem soft_window_loss_le {w eta eta' rho : ℝ} (hw : 0 < w) (hw1 : w ≤ 1)
    (heta' : 0 ≤ eta') (hle : eta' ≤ eta) (hrho0 : 0 ≤ rho)
    (hrho : rho ≤ w ^ 2 / (1000 * (8 * eta + 24))) :
    let h := w ^ 2 / (1000 * (8 * eta + 24))
    (⌈(eta' + h) / (2 * h)⌉₊ : ℝ) * (rho + h) ^ 2 / (w / 2 + h) ^ 2 ≤ 1 / 1000 := by
  intro h
  have heta : 0 ≤ eta := heta'.trans hle
  have hden : 0 < 1000 * (8 * eta + 24) := by positivity
  have hh : 0 < h := div_pos (by positivity) hden
  have hh1 : h ≤ 1 := by
    rw [div_le_one hden]
    nlinarith
  have hceil : (⌈(eta' + h) / (2 * h)⌉₊ : ℝ) ≤ (eta + h) / (2 * h) + 1 := by
    have h1 := Nat.ceil_lt_add_one (by positivity : 0 ≤ (eta' + h) / (2 * h))
    have h2 : (eta' + h) / (2 * h) ≤ (eta + h) / (2 * h) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    linarith
  have hnum : (rho + h) ^ 2 ≤ 4 * h ^ 2 := by nlinarith
  have hdenw : w ^ 2 / 4 ≤ (w / 2 + h) ^ 2 := by nlinarith
  have hw2 : 0 < w ^ 2 / 4 := by positivity
  calc (⌈(eta' + h) / (2 * h)⌉₊ : ℝ) * (rho + h) ^ 2 / (w / 2 + h) ^ 2
      ≤ ((eta + h) / (2 * h) + 1) * (4 * h ^ 2) / (w ^ 2 / 4) := by
        apply div_le_div₀ (by positivity) (mul_le_mul hceil hnum (by positivity)
          (by positivity)) hw2 hdenw
    _ = (8 * h * eta + 24 * h ^ 2) / w ^ 2 := by
        field_simp
        ring
    _ ≤ h * (8 * eta + 24) / w ^ 2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith
    _ = 1 / 1000 := by
        dsimp only [h]
        field_simp

/-- A precision `ξ ≤ w⁴ / (80000 (M + 8))` makes the perturbation loss at most `1 / 1000` for
every cutoff `|c| ≤ 67` and norm `R ≤ M + 2`. Numerical auxiliary to ALVV,
arXiv:1602.08828v2, `t:aisgaplessefficient`, lines 1446–1457. -/
theorem softWindowPerturbationLoss_le {R xi w c M : ℝ} (hw : 0 < w) (hw1 : w ≤ 1)
    (hM : 34 ≤ M) (hR : R ≤ M + 2) (hc : |c| ≤ 67) (hxi : 0 < xi)
    (hxi1 : xi ≤ 1) (hxiw : xi ≤ w ^ 4 / (80000 * (M + 8))) :
    softWindowPerturbationLoss R xi w c ≤ 1 / 1000 := by
  unfold softWindowPerturbationLoss
  set X := c - min (c - 1) (-(R + xi)) with hX
  have hcabs := abs_le.mp hc
  have hX1 : X ≤ M + 72 := by
    rcases min_choice (c - 1) (-(R + xi)) with h | h <;> rw [hX, h] <;> linarith
  have hX0 : 0 ≤ X := by
    have := min_le_left (c - 1) (-(R + xi))
    rw [hX]
    linarith
  have hceil : (⌈X / (2 * xi)⌉₊ : ℝ) ≤ X / (2 * xi) + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hdenw : w ^ 2 / 4 ≤ (w / 2 + xi) ^ 2 := by nlinarith
  have hw2 : 0 < w ^ 2 / 4 := by positivity
  calc (⌈X / (2 * xi)⌉₊ : ℝ) * (2 * xi) ^ 2 / (w / 2 + xi) ^ 2
      ≤ (X / (2 * xi) + 1) * (2 * xi) ^ 2 / (w ^ 2 / 4) :=
        div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hceil (by positivity))
          hw2 hdenw
    _ = (8 * X * xi + 16 * xi ^ 2) / w ^ 2 := by
        field_simp
        ring
    _ ≤ 8 * (M + 74) * xi / w ^ 2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith
    _ ≤ 8 * (M + 74) * (w ^ 4 / (80000 * (M + 8))) / w ^ 2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hxiw (by linarith)
    _ = (M + 74) * w ^ 2 / (10000 * (M + 8)) := by
        field_simp
        ring
    _ ≤ 1 / 1000 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        have hw2' : w ^ 2 ≤ 1 := by nlinarith
        nlinarith

/-- The contraction between two windows separated by at least `w / 2`, with lower cutoff at
least `-30` and ceiling `M ≥ 34`, is dominated by the contraction at the calibrated gap
`g = w² / 2`. Numerical auxiliary to ALVV, arXiv:1602.08828v2, `t:aisgaplessefficient`,
lines 1446–1457. -/
theorem soft_low_density_contraction_le {w c0 c1 M xi k : ℝ} (hw : 0 < w) (hw1 : w ≤ 1)
    (hM : 34 ≤ M) (hxi : 0 ≤ xi) (hk : 0 ≤ k) (hsep : w / 2 ≤ c1 - c0) (hc0 : -30 ≤ c0)
    (hc0M : c0 < M) :
    (2 * Real.exp (-2 * k * Real.sqrt ((c1 - c0) / (M + xi - c0)))) ^ 2 ≤
      (2 * Real.exp (-2 * k * Real.sqrt ((w ^ 2 / 2 / 2) / (M + xi + 4 + w ^ 2 / 2)))) ^ 2 := by
  apply pow_le_pow_left₀ (by positivity) _ 2
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.exp_le_exp.mpr
  have hsq : Real.sqrt ((w ^ 2 / 2 / 2) / (M + xi + 4 + w ^ 2 / 2)) ≤
      Real.sqrt ((c1 - c0) / (M + xi - c0)) := by
    apply Real.sqrt_le_sqrt
    have hden1 : 0 < M + xi + 4 + w ^ 2 / 2 := by positivity
    have hden2 : 0 < M + xi - c0 := by linarith
    rw [div_le_div_iff₀ hden1 hden2]
    have hw2 : w ^ 2 ≤ w := by nlinarith
    nlinarith
  nlinarith


/-- **Calibrated parameters for the efficient low-density family.** For fixed local dimension
`q ≥ 2` and buffer `w > 0`, one natural number `u ≥ 2` fixes `ℓ = u⁸`, `m = u¹⁰`, `t = 3 m`,
`k = u¹⁶`, `T = u⁹`, the count `D`, the norm ceiling `M`, `τ = (D²⁴ M¹⁰)⁻¹` and the precision
`ξ` at the gap `g = w² / 2`, such that the residual at the floor `156 + 2 g` is at most
`τ g / 10⁶`, the contraction at the gap `g` is at most `(D¹² M¹⁰)⁻¹`, and the member bond is
bounded by a natural polynomial in the chain length. Numerical auxiliary to ALVV,
arXiv:1602.08828v2, `t:aisgaplessefficient`, lines 1424–1437. -/
theorem exists_soft_low_density_calibration_data (q : ℕ) (hq : 2 ≤ q) (w : ℝ) (hw : 0 < w) :
    ∃ u : ℕ, 2 ≤ u ∧ ∃ Cpoly ppoly : ℕ, 1 ≤ Cpoly ∧
      ∀ (ell m k : ℕ) (t T Dc Mc tau g xi : ℝ),
        ell = u ^ 8 → m = u ^ 10 → t = 3 * (m : ℝ) → k = u ^ 16 → T = (u : ℝ) ^ 9 →
        Dc = (((m * k + 1) * (q * k) ^ (36 * ell + 4 * (k / ell)) : ℕ) : ℝ) →
        Mc = 3 * t * (1 + Real.log (m : ℝ)) + 4 * (ell : ℝ) + 34 →
        tau = 1 / (Dc ^ 24 * Mc ^ 10) → g = w ^ 2 / 2 →
        xi = min 1 (tau * g ^ 2 / (20000 * (Mc + g + 8))) →
        1 ≤ ell ∧ 2 ≤ m ∧ 1 ≤ k ∧ 156 + 2 * g ≤ t ∧ 156 + 2 * g ≤ T ∧
          0 < tau ∧ tau ≤ 1 ∧ 0 < xi ∧ xi ≤ 1 ∧ 1 ≤ Dc ∧
          3 * (32 * Real.exp (-(T - 156 - 2 * g) / 8) + (t / m) * (T / t) ^ m) ≤
            tau * g / 1000000 ∧
          (2 * Real.exp (-2 * (k : ℝ) * Real.sqrt ((g / 2) / (Mc + xi + 4 + g)))) ^ 2 ≤
            1 / (Dc ^ 12 * Mc ^ 10) ∧
          ∀ N : ℕ,
            let base := 2 * (Real.exp (1 / 3 : ℝ) - 1)
            let order := max 1 ⌈(Real.log (max 1 ((N : ℝ) ^ 2)) -
              Real.log (Real.log (1 + xi / (t * 2 ^ (m + 1))))) / (-Real.log base)⌉₊
            let B := ((order ^ 2 * q ^ order) * 2) * (m + 1)
            (max 1 B) ^ (2 * k) ≤ Cpoly * (N + 1) ^ ppoly := by
  obtain ⟨u, hu, hcal⟩ := Real.exists_soft_family_calibration q hq (w ^ 2 / 2)
    (by positivity) 24 10 10
  obtain ⟨hell, hm, hk, htfloor, hTfloor, _hT0, hD1, _hM1, htau, htau1,
    hxi, hxi1, _hO, hR, hDelta⟩ := hcal
  have hbase := TNLean.MPS.AreaLaw.softHeat_base_bounds
  obtain ⟨Cpoly, ppoly, hCpoly, hGeom⟩ := Real.exists_geometric_order_polynomial_bound
    (2 * (Real.exp (1 / 3 : ℝ) - 1)) (3 * ((u ^ 10 : ℕ) : ℝ) * 2 ^ (u ^ 10 + 1)) _
    hbase.1 hbase.2 (by positivity) hxi q (by omega) (u ^ 10 + 1) (u ^ 16)
  refine ⟨u, hu, Cpoly, ppoly, hCpoly, ?_⟩
  intro ell m k t T Dc Mc tau g xi hell' hm' ht' hk' hT' hDc hMc htau' hg' hxi'
  subst hell' hm' hk' hg' ht' hT' hDc hMc htau' hxi'
  refine ⟨hell, hm, hk, htfloor, hTfloor, htau, htau1, hxi, hxi1,
    by exact_mod_cast hD1, hR, hDelta, ?_⟩
  intro N base order B
  have hGeomN := hGeom N
  change (2 * (u ^ 10 + 1) * order ^ 2 * q ^ order) ^ (2 * u ^ 16) ≤
    Cpoly * (N + 1) ^ ppoly at hGeomN
  have horder : 0 < order := Nat.zero_lt_one.trans_le (le_max_left _ _)
  have hq0 : 0 < q := by omega
  have hBpos : 0 < B := by dsimp only [B]; positivity
  have hBform : B = 2 * (u ^ 10 + 1) * order ^ 2 * q ^ order := by
    dsimp only [B]
    ring
  rw [max_eq_right (show 1 ≤ B from hBpos), hBform]
  exact hGeomN


/-- **The calibrated losses.** Under the calibrated scalar data, for every band width
`3 w ≤ η ≤ 34`, with window resolution `h = w² / (1000 (8 η + 24))`, the residual scales are
at most `w² / (2 · 10⁶)`, all conditions of the efficient low-density family hold, both
closeness losses are at most `1 / 200`, and `D¹² Δ ≤ 10⁻⁵`. Numerical auxiliary to ALVV,
arXiv:1602.08828v2, `t:aisgaplessefficient`, lines 1446–1457. -/
theorem soft_low_density_calibrated_losses {w eta mu E t T Msoft xi tau g Cc D R : ℝ}
    {m k : ℕ} (hw : 0 < w) (hw1 : w ≤ 1) (h3w : 3 * w ≤ eta) (heta34 : eta ≤ 34)
    (hmu30 : -30 ≤ mu) (hmuE : mu ≤ E) (hE4 : E ≤ 4) (hC0 : 0 ≤ Cc) (hC4 : Cc ≤ 4)
    (hgdef : g = w ^ 2 / 2) (htfloor : 156 + 2 * g ≤ t) (hTfloor : 156 + 2 * g ≤ T)
    (htau1 : tau ≤ 1) (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    (hxidef : xi ≤ tau * g ^ 2 / (20000 * (Msoft + g + 8))) (hMs : 3 * t ≤ Msoft)
    (hR : 3 * (32 * Real.exp (-(T - 156 - 2 * g) / 8) + (t / m) * (T / t) ^ m) ≤
      tau * g / 1000000)
    (hDelta : (2 * Real.exp (-2 * (k : ℝ) * Real.sqrt ((g / 2) / (Msoft + xi + 4 + g)))) ^ 2 ≤
      1 / (D ^ 12 * Msoft ^ 10))
    (hD0 : 0 < D) (hRn : R ≤ Msoft + 2) :
    let hwin := w ^ 2 / (1000 * (8 * eta + 24))
    let eta1 := eta - 3 * w
    let eta2 := eta - w / 2
    let rhoH1 := 3 * ((8 * Cc) * Real.exp (-(T - eta1 - 3 * Cc - 12) / 8) +
      (t / (m : ℝ)) * (T / t) ^ m)
    let rho1 := 3 * ((8 * Cc) * Real.exp (-(T - 2 * (eta1 + 30 + 3 * Cc + 2)) / 8) +
      (t / (m : ℝ)) * (T / t) ^ m)
    let rho2 := 3 * ((8 * Cc) * Real.exp (-(T - 2 * (eta2 + 30 + 3 * Cc + 2)) / 8) +
      (t / (m : ℝ)) * (T / t) ^ m)
    let L1 := (⌈(eta1 + hwin) / (2 * hwin)⌉₊ : ℝ) * (rhoH1 + hwin) ^ 2 / (w / 2 + hwin) ^ 2
    let L2 := (⌈(eta2 + hwin) / (2 * hwin)⌉₊ : ℝ) * (rho2 + hwin) ^ 2 / (w / 2 + hwin) ^ 2
    let c1 := mu + eta - w
    let c0 := mu + eta - 2 * w + rho1
    let Delta := (2 * Real.exp (-2 * (k : ℝ) * Real.sqrt ((c1 - c0) / (Msoft + xi - c0)))) ^ 2
    0 < hwin ∧ 2 * (eta + 30 + 3 * Cc + 2) ≤ t ∧ 2 * (eta + 30 + 3 * Cc + 2) ≤ T ∧
      eta + 3 * Cc + 12 ≤ T ∧ rho1 ≤ w ^ 2 / 2000000 ∧ rho1 < w ∧
      2 * (L2 + softWindowPerturbationLoss R xi w c1) ≤ 1 / 200 ∧
      2 * (softWindowPerturbationLoss R xi w (c0 - w / 2) + L1) ≤ 1 / 200 ∧
      D ^ 12 * Delta ≤ 1 / 100000 := by
  intro hwin eta1 eta2 rhoH1 rho1 rho2 L1 L2 c1 c0 Delta
  have hg0 : 0 ≤ g := by rw [hgdef]; positivity
  have hM34 : 34 ≤ Msoft := by linarith
  have hres : 3 * (32 * Real.exp (-(T - (156 + 2 * g)) / 8) + (t / m) * (T / t) ^ m) ≤
      w ^ 2 / 2000000 := by
    rw [show T - (156 + 2 * g) = T - 156 - 2 * g by ring]
    refine hR.trans ?_
    rw [hgdef]
    have := mul_le_mul_of_nonneg_right htau1 (by positivity : (0 : ℝ) ≤ w ^ 2 / 2)
    linarith
  have hRrem : 0 ≤ (t / (m : ℝ)) * (T / t) ^ m := by
    have : 0 ≤ T := by linarith
    have : 0 ≤ t := by linarith
    positivity
  have hrhoN (x : ℝ) : 0 ≤ 3 * ((8 * Cc) * Real.exp x + (t / (m : ℝ)) * (T / t) ^ m) := by
    have h8 := mul_nonneg (by linarith : (0 : ℝ) ≤ 8 * Cc) (Real.exp_pos x).le
    linarith
  have hrho (V : ℝ) (hV : V ≤ 156 + 2 * g) :
      3 * ((8 * Cc) * Real.exp (-(T - V) / 8) + (t / (m : ℝ)) * (T / t) ^ m) ≤
        w ^ 2 / 2000000 :=
    soft_residual_le_of_floor_le hC4 hV hres
  have hrho1 : rho1 ≤ w ^ 2 / 2000000 := hrho _ (by dsimp only [eta1]; linarith)
  have hrho1' : 0 ≤ rho1 := hrhoN _
  have hw2 : w ^ 2 ≤ w := by nlinarith
  have hden : 0 < 1000 * (8 * eta + 24) := by linarith
  have hhwin : 0 < hwin := div_pos (by positivity) hden
  have hsmall : w ^ 2 / 2000000 ≤ hwin := by
    apply div_le_div_of_nonneg_left (by positivity) hden
    linarith
  have hL1 : L1 ≤ 1 / 1000 := soft_window_loss_le hw hw1 (by dsimp only [eta1]; linarith)
    (by dsimp only [eta1]; linarith) (hrhoN _)
    (by
      have hV := hrho (eta1 + 3 * Cc + 12) (by dsimp only [eta1]; linarith)
      have harg : -(T - eta1 - 3 * Cc - 12) / 8 = -(T - (eta1 + 3 * Cc + 12)) / 8 := by ring
      change 3 * ((8 * Cc) * Real.exp (-(T - eta1 - 3 * Cc - 12) / 8) +
        (t / (m : ℝ)) * (T / t) ^ m) ≤ hwin
      rw [harg]
      exact hV.trans hsmall)
  have hL2 : L2 ≤ 1 / 1000 := soft_window_loss_le hw hw1 (by dsimp only [eta2]; linarith)
    (by dsimp only [eta2]; linarith) (hrhoN _)
    ((hrho _ (by dsimp only [eta2]; linarith)).trans hsmall)
  have hxiw : xi ≤ w ^ 4 / (80000 * (Msoft + 8)) := by
    refine hxidef.trans ?_
    have hg2 : g ^ 2 = w ^ 4 / 4 := by rw [hgdef]; ring
    rw [hg2, div_le_div_iff₀ (by positivity) (by positivity)]
    have hw4 : 0 ≤ w ^ 4 := by positivity
    have h1 : tau * (w ^ 4 * (Msoft + 8)) ≤ 1 * (w ^ 4 * (Msoft + 8)) :=
      mul_le_mul_of_nonneg_right htau1 (mul_nonneg hw4 (by linarith))
    have h2 : 0 ≤ w ^ 4 * g := mul_nonneg hw4 hg0
    nlinarith only [h1, h2]
  have hP1 := softWindowPerturbationLoss_le (R := R) (c := c1) hw hw1 hM34 hRn
    (by rw [abs_le]; constructor <;> dsimp only [c1] <;> linarith) hxi hxi1 hxiw
  have hP0 := softWindowPerturbationLoss_le (R := R) (c := c0 - w / 2) hw hw1 hM34 hRn
    (by rw [abs_le]; constructor <;> dsimp only [c0] <;> linarith) hxi hxi1 hxiw
  have hDel : Delta ≤ 1 / (D ^ 12 * Msoft ^ 10) := by
    refine le_trans ?_ hDelta
    rw [hgdef]
    exact soft_low_density_contraction_le hw hw1 hM34 hxi.le (Nat.cast_nonneg k)
      (by dsimp only [c0, c1]; linarith) (by dsimp only [c0]; linarith)
      (by dsimp only [c0]; linarith)
  have hDD : D ^ 12 * Delta ≤ 1 / 100000 := by
    have hM10 : (100000 : ℝ) ≤ Msoft ^ 10 :=
      (by norm_num : (100000 : ℝ) ≤ 34 ^ 10).trans (pow_le_pow_left₀ (by norm_num) hM34 10)
    calc D ^ 12 * Delta ≤ D ^ 12 * (1 / (D ^ 12 * Msoft ^ 10)) :=
          mul_le_mul_of_nonneg_left hDel (by positivity)
      _ = 1 / Msoft ^ 10 := by field_simp
      _ ≤ 1 / 100000 := one_div_le_one_div_of_le (by norm_num) hM10
  refine ⟨hhwin, by linarith, by linarith, by linarith, hrho1, by linarith, by linarith,
    by linarith, hDD⟩

end TNLean.MPS.AreaLaw.ALVV

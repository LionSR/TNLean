/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Real.Sqrt

/-!
# Polynomial filter parameters

Here DG denotes the degenerate-ground-space setting of ALVV.

For fixed `C_H > 0` and any lower threshold `M`, one constant `A` controls
both the polynomial count and a squared exponential contraction. With
`u = 1 + log d + log (1 / g)`, `ell = ceil (A * u^2 / g)` and
`D = (d * ell^2)^(22 * ell)`, the theorem bounds `log D` by a constant
multiple of `u^3 / g` and proves `D^12 * Delta ≤ 1 / 100000` for
`Delta = 4 * exp (-4 * ell^2 * sqrt ((4 * g / 5) / R))` whenever
`d ≥ 2`, `0 < g ≤ 1` and `0 < R ≤ 2 * C_H * ell`.

The same choice of `A` controls every scalar tail whose fixed coefficients
have threshold at most `M`. That threshold enters the choice of `A`, so one
constant satisfies the count, contraction and all eligible tail estimates.

This is a supporting scalar estimate for Arad, Landau, Vazirani and Vidick,
arXiv:1602.08828v2, Theorem `t:ais`, lines 1010–1024. These parameters apply
once the spectral width and truncation constants have been derived for the
local Hamiltonian.
-/

open Filter

/-- At the chosen square degree the original integer count exponent is
exactly 22 times the positive scale. Auxiliary to ALVV, t:ais. -/
private theorem Nat.count_exponent_eq (ell : ℕ) (hell : 0 < ell) :
    20 * ell + 2 * (ell ^ 2 / ell) = 22 * ell := by
  rw [pow_two, Nat.mul_div_right _ hell]
  ring

namespace Real

/-- A logarithmic expression is eventually bounded by any positive multiple
of the square root, beyond any prescribed lower bound. This is a scalar
estimate supporting ALVV, arXiv:1602.08828v2, lines 1010–1024. -/
private theorem exists_log_sqrt_absorption (a b c M : ℝ) (hb : 0 ≤ b) (hc : 0 < c) :
    ∃ A : ℝ, 1 ≤ A ∧ M ≤ A ∧ a + b * log (A + 1) ≤ c * sqrt A := by
  have hlog : log =o[atTop] sqrt := by
    change log =o[atTop] (fun x : ℝ ↦ sqrt x)
    simpa only [sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (show 0 < (1 / (2 : ℝ)) by norm_num))
  have hconst : (fun _ : ℝ ↦ a + b * log 2) =o[atTop] sqrt := by
    simpa only [Function.comp_def, id_eq] using
      (Asymptotics.isLittleO_const_id_atTop (a + b * log 2)).comp_tendsto
        tendsto_sqrt_atTop
  have hsmall : (fun x : ℝ ↦ a + b * log 2 + b * log x) =o[atTop] sqrt :=
    hconst.add (hlog.const_mul_left b)
  obtain ⟨A, hA, hbound⟩ :=
    ((eventually_ge_atTop (max 1 M)).and (hsmall.def hc)).exists
  have hA1 : 1 ≤ A := (le_max_left 1 M).trans hA
  have hAM : M ≤ A := (le_max_right 1 M).trans hA
  have hlogA : log (A + 1) ≤ log 2 + log A := by
    calc
      log (A + 1) ≤ log (2 * A) := log_le_log (by linarith) (by linarith)
      _ = log 2 + log A := log_mul (by norm_num) (by linarith)
  refine ⟨A, hA1, hAM, ?_⟩
  calc
    a + b * log (A + 1) ≤ a + b * (log 2 + log A) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hlogA hb) a
    _ = a + b * log 2 + b * log A := by ring
    _ ≤ ‖a + b * log 2 + b * log A‖ := le_abs_self _
    _ ≤ c * ‖sqrt A‖ := hbound
    _ = c * sqrt A := by rw [Real.norm_eq_abs, abs_of_nonneg (sqrt_nonneg A)]

/-- The ceiling of A v²/g is bounded above by (A+1)v²/g and below by A.
Auxiliary to ALVV, arXiv:1602.08828v2, Theorem `t:ais`, lines 1010–1024. -/
private theorem ceil_scale_bounds (A v g : ℝ) (hA : 1 ≤ A) (hv : 1 ≤ v)
    (hg : 0 < g) (hg1 : g ≤ 1) :
    A * v ^ 2 / g ≤ (⌈A * v ^ 2 / g⌉₊ : ℝ) ∧
      (⌈A * v ^ 2 / g⌉₊ : ℝ) ≤ (A + 1) * v ^ 2 / g ∧
      A ≤ (⌈A * v ^ 2 / g⌉₊ : ℝ) := by
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hv2 : 1 ≤ v ^ 2 := by nlinarith
  have hratio : 1 ≤ v ^ 2 / g := (le_div_iff₀ hg).2 (by linarith)
  have hnonneg : 0 ≤ A * v ^ 2 / g :=
    div_nonneg (mul_nonneg hA0 (sq_nonneg v)) hg.le
  have hscale : A ≤ A * v ^ 2 / g := by
    calc
      A = A * 1 := (mul_one A).symm
      _ ≤ A * (v ^ 2 / g) := mul_le_mul_of_nonneg_left hratio hA0
      _ = A * v ^ 2 / g := by ring
  have hlower : A * v ^ 2 / g ≤ (⌈A * v ^ 2 / g⌉₊ : ℝ) := Nat.le_ceil _
  refine ⟨hlower, ?_, hscale.trans hlower⟩
  calc
    (⌈A * v ^ 2 / g⌉₊ : ℝ) ≤ A * v ^ 2 / g + 1 :=
      (Nat.ceil_lt_add_one hnonneg).le
    _ ≤ A * v ^ 2 / g + v ^ 2 / g := add_le_add le_rfl hratio
    _ = (A + 1) * v ^ 2 / g := by ring

/-- Joint choice of the logarithmic absorption constant and a prescribed
lower threshold. Scalar auxiliary for ALVV, t:ais, lines 1010--1024. -/
private theorem joint_absorption_constant (C_H M : ℝ) (hC : 0 < C_H) :
    ∃ A : ℝ, 1 ≤ A ∧ 21 ≤ A ∧ M ≤ A ∧ log 400000 ≤ A ∧
      264 * (6 + 2 * log (A + 1)) + 1 ≤
        4 * sqrt (2 * A / (5 * C_H)) := by
  have hc : 0 < 4 * sqrt (2 / (5 * C_H)) := by positivity
  obtain ⟨A, hA, hM, hbound⟩ := exists_log_sqrt_absorption
    1585 528 (4 * sqrt (2 / (5 * C_H)))
    (max M (max 21 (log 400000))) (by norm_num) hc
  refine ⟨A, hA, ?_, ?_, ?_, ?_⟩
  · exact (le_max_left 21 (log 400000)).trans ((le_max_right M _).trans hM)
  · exact (le_max_left M _).trans hM
  · exact (le_max_right 21 (log 400000)).trans ((le_max_right M _).trans hM)
  · calc
      264 * (6 + 2 * log (A + 1)) + 1 =
          1585 + 528 * log (A + 1) := by ring
      _ ≤ (4 * sqrt (2 / (5 * C_H))) * sqrt A := hbound
      _ = 4 * sqrt (2 * A / (5 * C_H)) := by
        rw [show 2 * A / (5 * C_H) = (2 / (5 * C_H)) * A by ring,
          sqrt_mul (show 0 ≤ 2 / (5 * C_H) by positivity)]
        ring

/-- The logarithm of the actual count base is linear in the logarithmic
scale. Scalar auxiliary for ALVV, t:ais, lines 1010--1024. -/
private theorem log_base_bound (A d g u e : ℝ) (hA : 1 ≤ A)
    (hd : 2 ≤ d) (hg : 0 < g) (hg1 : g ≤ 1)
    (hu : u = 1 + log d + log (1 / g))
    (he : 1 ≤ e) (heup : e ≤ (A + 1) * u ^ 2 / g) :
    log (d * e ^ 2) ≤ (6 + 2 * log (A + 1)) * u := by
  have hd0 : 0 < d := by linarith
  have hb : 0 ≤ log (1 / g) := log_nonneg ((one_le_div hg).2 hg1)
  have hld : 0 ≤ log d := log_nonneg (by linarith)
  have hu1 : 1 ≤ u := by rw [hu]; linarith
  have hu0 : 0 < u := by linarith
  have he0 : 0 < e := by linarith
  have hAp : 0 < A + 1 := by linarith
  have hla : 0 ≤ log (A + 1) := log_nonneg (by linarith)
  have hle : log e ≤ log (A + 1) + 2 * log u + log (1 / g) := by
    calc
      log e ≤ log ((A + 1) * u ^ 2 / g) := log_le_log he0 heup
      _ = log (A + 1) + 2 * log u + log (1 / g) := by
        rw [log_div (mul_ne_zero hAp.ne' (pow_ne_zero 2 hu0.ne')) hg.ne',
          log_mul hAp.ne' (pow_ne_zero 2 hu0.ne'), log_pow,
          one_div, log_inv]
        ring
  have hlu : log u ≤ u := log_le_self hu0.le
  have hldg : log d + 2 * log (1 / g) ≤ 2 * u := by rw [hu]; linarith
  have hlaMul : log (A + 1) ≤ log (A + 1) * u := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hu1 hla
  calc
    log (d * e ^ 2) = log d + 2 * log e := by
      rw [log_mul hd0.ne' (pow_ne_zero 2 he0.ne'), log_pow]
      norm_num
    _ ≤ log d + 2 * (log (A + 1) + 2 * log u + log (1 / g)) := by
      linarith only [hle]
    _ ≤ 2 * log (A + 1) + 6 * u := by
      linarith only [hlu, hldg]
    _ ≤ (6 + 2 * log (A + 1)) * u := by
      nlinarith only [hlaMul]

/-- The width bound and the ceiling lower bound give the required decay
exponent. This is scalar algebra, not a physical spectral-width estimate. -/
private theorem decay_exponent_lower (C_H A g u e R : ℝ)
    (hC : 0 < C_H) (hA : 0 ≤ A) (hg : 0 < g)
    (hu : 0 ≤ u) (he : 0 ≤ e) (hR : 0 < R)
    (hRup : R ≤ 2 * C_H * e) (hscale : A * u ^ 2 ≤ g * e) :
    4 * e * u * sqrt (2 * A / (5 * C_H)) ≤
      4 * e ^ 2 * sqrt ((4 * g / 5) / R) := by
  have hcross : A * u ^ 2 * R ≤ 2 * C_H * g * e ^ 2 := by
    calc
      A * u ^ 2 * R ≤ A * u ^ 2 * (2 * C_H * e) :=
        mul_le_mul_of_nonneg_left hRup (mul_nonneg hA (sq_nonneg u))
      _ ≤ (g * e) * (2 * C_H * e) :=
        mul_le_mul_of_nonneg_right hscale (by positivity)
      _ = 2 * C_H * g * e ^ 2 := by ring
  have hsquare :
      (u * sqrt (2 * A / (5 * C_H))) ^ 2 ≤
        (e * sqrt ((4 * g / 5) / R)) ^ 2 := by
    rw [mul_pow, mul_pow, sq_sqrt (by positivity), sq_sqrt (by positivity)]
    calc
      u ^ 2 * (2 * A / (5 * C_H)) = (2 * A * u ^ 2) / (5 * C_H) := by ring
      _ ≤ (4 * g * e ^ 2) / (5 * R) := by
        apply (div_le_div_iff₀ (by positivity : 0 < 5 * C_H)
          (by positivity : 0 < 5 * R)).2
        nlinarith only [hcross]
      _ = e ^ 2 * ((4 * g / 5) / R) := by ring
  have hroot : u * sqrt (2 * A / (5 * C_H)) ≤
      e * sqrt ((4 * g / 5) / R) :=
    (sq_le_sq₀ (by positivity) (by positivity)).mp hsquare
  have hmul := mul_le_mul_of_nonneg_left hroot (show 0 ≤ 4 * e by positivity)
  nlinarith only [hmul]

/-- An explicit lower threshold controls a scalar exponential tail with the
same integer scale. No physical truncation estimate is asserted. -/
private theorem scalar_tail_bound (A u g e C c epsilon p : ℝ)
    (hu : 1 + log (1 / g) ≤ u)
    (hg : 0 < g) (hg1 : g ≤ 1) (hscale : A * u ≤ e)
    (hC : 0 < C) (hc : 0 < c) (hepsilon : 0 < epsilon) (hp : 0 ≤ p)
    (hthreshold : (max 0 (log (C / epsilon)) + p + c) / c ≤ A) :
    C * exp (-c * (e - g)) ≤ epsilon * g ^ p := by
  have hb : 0 ≤ log (1 / g) := log_nonneg ((one_le_div hg).2 hg1)
  have hu1 : 1 ≤ u := by linarith
  have hB0 : 0 ≤ max 0 (log (C / epsilon)) := le_max_left _ _
  have hB : log (C / epsilon) ≤ max 0 (log (C / epsilon)) := le_max_right _ _
  have hAcoef : max 0 (log (C / epsilon)) + p + c ≤ c * A := by
    have h := (div_le_iff₀ hc).mp hthreshold
    nlinarith only [h]
  have hbase : max 0 (log (C / epsilon)) + c ≤
      (max 0 (log (C / epsilon)) + c) * u := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hu1 (add_nonneg hB0 hc.le)
  have hpterm : p * log (1 / g) ≤ p * u :=
    mul_le_mul_of_nonneg_left (by linarith) hp
  have hexponent : log (C / epsilon) + p * log (1 / g) ≤ c * (e - g) := by
    have hcoef := mul_le_mul_of_nonneg_right hAcoef (show 0 ≤ u by linarith)
    have he := mul_le_mul_of_nonneg_left hscale hc.le
    have hcg := mul_le_mul_of_nonneg_left hg1 hc.le
    nlinarith only [hB, hbase, hpterm, hcoef, he, hcg]
  calc
    C * exp (-c * (e - g)) ≤
        C * exp (-(log (C / epsilon) + p * log (1 / g))) :=
      mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith)) hC.le
    _ = epsilon * g ^ p := by
      rw [log_div hC.ne' hepsilon.ne', one_div, log_inv, rpow_def_of_pos hg]
      rw [show -(log C - log epsilon + p * -log g) =
        log epsilon - log C + log g * p by ring, exp_add, exp_sub,
        exp_log hepsilon, exp_log hC]
      field_simp [hC.ne']

/-- Joint scalar choice for the actual DG count and squared contraction.
This supporting statement for ALVV, t:ais, lines 1010--1024, does not assert
any physical Hamiltonian or hard-truncation estimate. -/
theorem exists_dg_scalar_parameters (C_H M : ℝ) (hC : 0 < C_H) :
    ∃ A : ℝ, 1 ≤ A ∧ 21 ≤ A ∧ M ≤ A ∧ log 400000 ≤ A ∧
      ∀ (d : ℕ) (g : ℝ), 2 ≤ d → 0 < g → g ≤ 1 →
      let u : ℝ := 1 + log (d : ℝ) + log (1 / g)
      let ell : ℕ := ⌈A * u ^ 2 / g⌉₊
      let D : ℕ := (d * ell ^ 2) ^ (22 * ell)
      let cA : ℝ := 6 + 2 * log (A + 1)
      A * u ^ 2 / g ≤ (ell : ℝ) ∧
      (ell : ℝ) ≤ (A + 1) * u ^ 2 / g ∧ A ≤ (ell : ℝ) ∧
      20 * ell + 2 * (ell ^ 2 / ell) = 22 * ell ∧
      log (D : ℝ) ≤ 22 * (A + 1) * cA / g * u ^ 3 ∧
      (∀ R : ℝ, 0 < R → R ≤ 2 * C_H * (ell : ℝ) →
        (D : ℝ) ^ 12 *
          (4 * exp (-(4 * (ell : ℝ) ^ 2 * sqrt ((4 * g / 5) / R)))) ≤
            1 / 100000) ∧
      (∀ C c epsilon p : ℝ, 0 < C → 0 < c → 0 < epsilon → 0 ≤ p →
        (max 0 (log (C / epsilon)) + p + c) / c ≤ M →
        C * exp (-c * ((ell : ℝ) - g)) ≤ epsilon * g ^ p) := by
  obtain ⟨A, hA, hA21, hAM, hAlog, habsorb⟩ := joint_absorption_constant C_H M hC
  refine ⟨A, hA, hA21, hAM, hAlog, ?_⟩
  intro d g hd hg hg1 u ell D cA
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd0 : 0 < (d : ℝ) := by linarith
  have hld : 0 ≤ log (d : ℝ) := log_nonneg (by linarith)
  have hb : 0 ≤ log (1 / g) := log_nonneg ((one_le_div hg).2 hg1)
  have hu1 : 1 ≤ u := by dsimp only [u]; linarith
  have hu0 : 0 ≤ u := by linarith
  obtain ⟨hellLower, hellUpper, hellA⟩ := ceil_scale_bounds A u g hA hu1 hg hg1
  have hell1 : 1 ≤ (ell : ℝ) := hA.trans hellA
  have hell0 : 0 ≤ (ell : ℝ) := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hcA0 : 0 ≤ cA := by
    dsimp only [cA]
    have := log_nonneg (show 1 ≤ A + 1 by linarith)
    linarith
  have hbase : log ((d : ℝ) * (ell : ℝ) ^ 2) ≤ cA * u :=
    log_base_bound A d g u ell hA hdR hg hg1 rfl hell1 hellUpper
  have hDcast : (D : ℝ) = ((d : ℝ) * (ell : ℝ) ^ 2) ^ (22 * ell) := by
    simp only [D, Nat.cast_pow, Nat.cast_mul]
  have hDpos : 0 < (D : ℝ) := by rw [hDcast]; positivity
  have hlogD : log (D : ℝ) ≤ 22 * (ell : ℝ) * cA * u := by
    rw [hDcast, log_pow]
    have hmul := mul_le_mul_of_nonneg_left hbase
      (show 0 ≤ 22 * (ell : ℝ) by positivity)
    push_cast
    nlinarith only [hmul]
  have hlogDup : log (D : ℝ) ≤ 22 * (A + 1) * cA / g * u ^ 3 := by
    have hmul := mul_le_mul_of_nonneg_right hellUpper
      (show 0 ≤ 22 * cA * u by positivity)
    calc
      log (D : ℝ) ≤ 22 * (ell : ℝ) * cA * u := hlogD
      _ ≤ 22 * ((A + 1) * u ^ 2 / g) * cA * u := by nlinarith only [hmul]
      _ = 22 * (A + 1) * cA / g * u ^ 3 := by ring
  have hscale : A * u ^ 2 ≤ g * (ell : ℝ) := by
    have h := (div_le_iff₀ hg).mp hellLower
    nlinarith only [h]
  have hAu : A * u ≤ (ell : ℝ) := by
    have huu : u ≤ u ^ 2 := by nlinarith only [hu1]
    have h1 := mul_le_mul_of_nonneg_left huu hA0
    have h2 := mul_le_mul_of_nonneg_right hg1 hell0
    nlinarith only [h1, h2, hscale]
  have hellpos : 0 < ell := by
    exact_mod_cast (show 0 < (ell : ℝ) by linarith)
  refine ⟨hellLower, hellUpper, hellA, Nat.count_exponent_eq ell hellpos, hlogDup, ?_, ?_⟩
  · intro R hR hRup
    let E : ℝ := 4 * (ell : ℝ) ^ 2 * sqrt ((4 * g / 5) / R)
    have hE : 4 * (ell : ℝ) * u * sqrt (2 * A / (5 * C_H)) ≤ E :=
      decay_exponent_lower C_H A g u ell R hC hA0 hg hu0 hell0 hR hRup hscale
    have hmargin : 264 * (ell : ℝ) * cA * u + (ell : ℝ) * u ≤ E := by
      calc
        264 * (ell : ℝ) * cA * u + (ell : ℝ) * u =
            ((ell : ℝ) * u) * (264 * cA + 1) := by ring
        _ ≤ ((ell : ℝ) * u) * (4 * sqrt (2 * A / (5 * C_H))) :=
          mul_le_mul_of_nonneg_left habsorb (mul_nonneg hell0 hu0)
        _ ≤ E := by nlinarith only [hE]
    have hellu : A ≤ (ell : ℝ) * u := by
      exact hellA.trans (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hu1 hell0)
    have hdecay : 12 * log (D : ℝ) - E ≤ -A := by
      nlinarith only [hlogD, hmargin, hellu]
    have hDexp : (D : ℝ) ^ 12 = exp (12 * log (D : ℝ)) := by
      calc
        (D : ℝ) ^ 12 = (exp (log (D : ℝ))) ^ 12 := by rw [exp_log hDpos]
        _ = exp (12 * log (D : ℝ)) := by
          simpa only [Nat.cast_ofNat] using (exp_nat_mul (log (D : ℝ)) 12).symm
    calc
      (D : ℝ) ^ 12 * (4 * exp (-E)) =
          4 * exp (12 * log (D : ℝ) - E) := by
        rw [hDexp, sub_eq_add_neg, exp_add]
        ring
      _ ≤ 4 * exp (-A) :=
        mul_le_mul_of_nonneg_left (exp_le_exp.mpr hdecay) (by norm_num)
      _ ≤ 4 * exp (-log 400000) :=
        mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith)) (by norm_num)
      _ = 1 / 100000 := by
        rw [exp_neg, exp_log (show 0 < (400000 : ℝ) by norm_num)]
        norm_num
  · intro C c epsilon p hCp hcp hep hp hMtail
    apply scalar_tail_bound A u g ell C c epsilon p
      (by dsimp only [u]; linarith) hg hg1 hAu hCp hcp hep hp
    exact hMtail.trans hAM

end Real


section

section

open Filter

open scoped Topology

namespace Real

/-- A single universal constant gives the integer scale, count, exponential
truncation tail and squared Chebyshev tradeoff used in the physical DG
construction. This is a scalar specialization supporting ALVV,
arXiv:1602.08828v2, Theorem `t:ais`, lines 1010–1024. It does not itself
assert the spectral or operator-family conclusions of that theorem. -/
theorem exists_physical_dg_scalar_parameters :
    let Ctail : ℝ := 288 * exp (11 / 8)
    let M : ℝ := (max 0 (log (Ctail / (1 / 1000000))) + 1 + 1 / 8) / (1 / 8)
    ∃ A : ℝ, 1 ≤ A ∧ 21 ≤ A ∧ M ≤ A ∧ log 400000 ≤ A ∧
      ∀ (d : ℕ) (g : ℝ), 2 ≤ d → 0 < g → g ≤ 1 →
      let u : ℝ := 1 + log (d : ℝ) + log (1 / g)
      let ell : ℕ := ⌈A * u ^ 2 / g⌉₊
      let D : ℕ := (d * ell ^ 2) ^ (22 * ell)
      let cA : ℝ := 6 + 2 * log (A + 1)
      21 ≤ ell ∧ 2 ≤ D ∧
      A * u ^ 2 / g ≤ (ell : ℝ) ∧
      (ell : ℝ) ≤ (A + 1) * u ^ 2 / g ∧ A ≤ (ell : ℝ) ∧
      20 * ell + 2 * (ell ^ 2 / ell) = 22 * ell ∧
      log (D : ℝ) ≤ 22 * (A + 1) * cA / g * u ^ 3 ∧
      (∀ R : ℝ, 0 < R → R ≤ 8 * (ell : ℝ) →
        (D : ℝ) ^ 12 *
          (4 * exp (-(4 * (ell : ℝ) ^ 2 * sqrt ((4 * g / 5) / R)))) ≤
            1 / 100000) ∧
      Ctail * exp (-((ell : ℝ) - g) / 8) ≤ g / 1000000 := by
  intro Ctail M
  obtain ⟨A, hA, hA21, hAM, hAlog, hall⟩ :=
    exists_dg_scalar_parameters 4 M (by norm_num)
  refine ⟨A, hA, hA21, hAM, hAlog, ?_⟩
  intro d g hd hg hg1 u ell D cA
  obtain ⟨hlower, hupper, hscale, hcount, hlogD, htrade, htail⟩ :=
    hall d g hd hg hg1
  have hellR : (21 : ℝ) ≤ (ell : ℝ) := hA21.trans hscale
  have hell : 21 ≤ ell := by exact_mod_cast hellR
  have hell1 : 1 ≤ ell := by omega
  have hbase : 2 ≤ d * ell ^ 2 := by
    calc
      2 ≤ d := hd
      _ = d * 1 := (mul_one d).symm
      _ ≤ d * ell ^ 2 := Nat.mul_le_mul_left d (Left.one_le_pow_of_le hell1 2)
  have hD : 2 ≤ D := hbase.trans
    (le_self_pow (by omega : 1 ≤ d * ell ^ 2)
      (Nat.mul_ne_zero (by norm_num) (by omega : ell ≠ 0)))
  refine ⟨hell, hD, hlower, hupper, hscale, hcount, hlogD, ?_, ?_⟩
  · intro R hR hRup
    apply htrade R hR
    simpa only [show (2 : ℝ) * 4 = 8 by norm_num] using hRup
  · have hCtail : 0 < Ctail := by
      dsimp only [Ctail]
      positivity
    have h := htail Ctail (1 / 8) (1 / 1000000) 1
      hCtail (by norm_num) (by norm_num) (by norm_num) le_rfl
    have harg : -(1 / 8 : ℝ) * ((ell : ℝ) - g) =
        -((ell : ℝ) - g) / 8 := by ring
    rw [harg, rpow_one] at h
    simpa only [div_mul_eq_mul_div, one_mul] using h
end Real
end

section

namespace Real

/-- The physical spectral endpoints give a positive Chebyshev width within
the joint scalar budget. The squared filter error has exactly the decay
expression used by that budget. Auxiliary to ALVV, arXiv:1602.08828v2,
Definition `def:Cheby-AGSP` and Theorem `thm:Cheby-AGSP`, lines 789–853,
and Theorem `t:ais`, lines 1010–1024. -/
theorem physical_chebyshev_endpoints
    (ell : ℕ) (E0 g : ℝ) (hell : 21 ≤ ell)
    (hE0 : 0 ≤ E0) (hE4 : E0 ≤ 4) (hg : 0 < g) (hg1 : g ≤ 1) :
    let eta0 := E0 + g / 10
    let eta1 := E0 + 9 * g / 10
    let upper := 7 * (ell : ℝ)
    let R := upper - eta0
    eta0 < eta1 ∧ eta1 ≤ upper ∧ 0 < R ∧ R ≤ 8 * (ell : ℝ) ∧
      eta1 - eta0 = 4 * g / 5 ∧
      (2 * exp (-2 * (ell : ℝ) ^ 2 * sqrt ((eta1 - eta0) / R))) ^ 2 =
        4 * exp (-4 * (ell : ℝ) ^ 2 * sqrt ((4 * g / 5) / R)) := by
  intro eta0 eta1 upper R
  have hellR : 21 ≤ (ell : ℝ) := by exact_mod_cast hell
  have hsep : eta0 < eta1 := by dsimp only [eta0, eta1]; linarith
  have hupper : eta1 ≤ upper := by dsimp only [eta1, upper]; linarith
  have hR0 : 0 < R := by dsimp only [R]; linarith
  have hR8 : R ≤ 8 * (ell : ℝ) := by
    dsimp only [R, upper, eta0]
    linarith
  have hgap : eta1 - eta0 = 4 * g / 5 := by dsimp only [eta0, eta1]; ring
  refine ⟨hsep, hupper, hR0, hR8, hgap, ?_⟩
  rw [hgap]
  let z := -2 * (ell : ℝ) ^ 2 * sqrt ((4 * g / 5) / R)
  change (2 * exp z) ^ 2 = 4 * exp (-4 * (ell : ℝ) ^ 2 * sqrt ((4 * g / 5) / R))
  calc
    _ = 4 * (exp z * exp z) := by ring
    _ = 4 * exp (z + z) := by rw [exp_add]
    _ = _ := by congr 2; dsimp only [z]; ring
end Real
end
end

section

namespace TNLean.MPS.AreaLaw

/-- At degree `ell ^ 2`, adjoining at most `2 * ell` collar sites fits the
square family bound with exponent `22 * ell`. The old family contributes
`18 * ell + 2 * (ell ^ 2 / ell)` to its unsquared exponent; the containing-region
transfer contributes `q ^ (2 * d)` to its cardinality.
Auxiliary to ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1311–1333,
and Theorem `t:ais`, lines 1010–1024. -/
theorem collar_card_le_square_at_square_degree (q ell d n : ℕ)
    (hq : 2 ≤ q) (hell : 1 ≤ ell) (hd : d ≤ 2 * ell)
    (hn : n ≤ ((q * ell ^ 2) ^ (18 * ell + 2 * (ell ^ 2 / ell))) ^ 2) :
    n * q ^ (2 * d) ≤ ((q * ell ^ 2) ^ (22 * ell)) ^ 2 := by
  have hellPos : 0 < ell := by omega
  have hdiv : ell ^ 2 / ell = ell := by
    rw [pow_two]
    exact Nat.mul_div_cancel ell hellPos
  have hexp : 18 * ell + 2 * (ell ^ 2 / ell) = 20 * ell := by
    rw [hdiv]
    omega
  let b := q * ell ^ 2
  have hsq : 1 ≤ ell ^ 2 := by
    rw [pow_two]
    simpa only [Nat.one_mul] using Nat.mul_le_mul hell hell
  have hbase : q ≤ b := by
    dsimp only [b]
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left q hsq
  have hbPos : 0 < b := by omega
  have hn' : n ≤ (b ^ (20 * ell)) ^ 2 := by
    simpa only [b, hexp] using hn
  have hfactor : q ^ (2 * d) ≤ b ^ (4 * ell) :=
    Nat.le_trans (Nat.pow_le_pow_left hbase (2 * d))
      (Nat.pow_le_pow_right hbPos (by omega))
  change n * q ^ (2 * d) ≤ (b ^ (22 * ell)) ^ 2
  calc
    n * q ^ (2 * d) ≤ (b ^ (20 * ell)) ^ 2 * b ^ (4 * ell) :=
      Nat.mul_le_mul hn' hfactor
    _ = b ^ ((20 * ell) * 2) * b ^ (4 * ell) :=
      congrArg (fun t : ℕ ↦ t * b ^ (4 * ell)) (pow_mul b (20 * ell) 2).symm
    _ = b ^ ((20 * ell) * 2 + 4 * ell) := (pow_add b _ _).symm
    _ = b ^ ((22 * ell) * 2) := by
      congr 1
      omega
    _ = (b ^ (22 * ell)) ^ 2 := pow_mul b (22 * ell) 2
end TNLean.MPS.AreaLaw
end


section

open Filter

open scoped Topology

namespace Real

/-- A single scalar choice gives an accuracy-dependent truncation tail with
an auxiliary numerical count base. The physical local dimension need not
equal this base. This supports the dyadic entropy argument for ALVV,
arXiv:1602.08828v2, `thm:al-dg`, lines 1048–1099, using the parameter
choice in `t:ais`, lines 1010–1024. No physical spectral or operator-family
assertion, padding of sites, or enlargement of a previously chosen constant
is made here. -/
theorem exists_dg_accuracy_scalar_parameters :
    let Ctail : ℝ := 288 * exp (11 / 8)
    let Caug : ℝ := Ctail * exp (1 / 8)
    let Maug : ℝ :=
      (max 0 (log (Caug / (1 / 1000000))) + 1 + 1 / 8) / (1 / 8)
    ∃ A : ℝ, 1 ≤ A ∧ 21 ≤ A ∧ Maug ≤ A ∧ log 400000 ≤ A ∧
      ∀ (m : ℕ) (g : ℝ), 2 ≤ m → 0 < g → g ≤ 1 →
      let u : ℝ := 1 + log (m : ℝ) + log (1 / g)
      let ell : ℕ := ⌈A * u ^ 2 / g⌉₊
      let D : ℕ := (m * ell ^ 2) ^ (22 * ell)
      let cA : ℝ := 6 + 2 * log (A + 1)
      21 ≤ ell ∧ m ≤ D ∧ 2 ≤ D ∧
      A * u ^ 2 / g ≤ (ell : ℝ) ∧
      (ell : ℝ) ≤ (A + 1) * u ^ 2 / g ∧ A ≤ (ell : ℝ) ∧
      20 * ell + 2 * (ell ^ 2 / ell) = 22 * ell ∧
      log (D : ℝ) ≤ 22 * (A + 1) * cA / g * u ^ 3 ∧
      (∀ R : ℝ, 0 < R → R ≤ 8 * (ell : ℝ) →
        (D : ℝ) ^ 12 *
          (4 * exp (-(4 * (ell : ℝ) ^ 2 * sqrt ((4 * g / 5) / R)))) ≤
            1 / 100000) ∧
      Ctail * exp (-((ell : ℝ) - g) / 8) ≤ g / (1000000 * (m : ℝ)) := by
  intro Ctail Caug Maug
  obtain ⟨A, hA, hA21, hAM, hAlog, hall⟩ :=
    exists_dg_scalar_parameters 4 Maug (by norm_num)
  refine ⟨A, hA, hA21, hAM, hAlog, ?_⟩
  intro m g hm hg hg1 u ell D cA
  obtain ⟨hlower, hupper, hscale, hcount, hlogD, htrade, _htail⟩ :=
    hall m g hm hg hg1
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmRpos : 0 < (m : ℝ) := by linarith
  have hmR1 : (1 : ℝ) ≤ (m : ℝ) := by linarith
  have hellR : (21 : ℝ) ≤ (ell : ℝ) := hA21.trans hscale
  have hell : 21 ≤ ell := by exact_mod_cast hellR
  have hell1 : 1 ≤ ell := by omega
  have hbase : m ≤ m * ell ^ 2 := by
    simpa only [mul_one] using
      Nat.mul_le_mul_left m (Left.one_le_pow_of_le hell1 2)
  have hmD : m ≤ D := hbase.trans
    (le_self_pow (by omega : 1 ≤ m * ell ^ 2)
      (Nat.mul_ne_zero (by norm_num) (by omega : ell ≠ 0)))
  have hlogm : 0 ≤ log (m : ℝ) := log_nonneg hmR1
  have hlogg : 0 ≤ log (1 / g) := log_nonneg ((one_le_div hg).2 hg1)
  have hu1 : 1 ≤ u := by dsimp only [u]; linarith
  have hAu : A * u ≤ (ell : ℝ) := by
    calc
      A * u ≤ A * u ^ 2 :=
        mul_le_mul_of_nonneg_left (by nlinarith : u ≤ u ^ 2) (by linarith)
      _ ≤ (ell : ℝ) * g := (div_le_iff₀ hg).mp hlower
      _ ≤ (ell : ℝ) := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hg1 (Nat.cast_nonneg ell)
  let gp : ℝ := g / (m : ℝ)
  have hgp : 0 < gp := div_pos hg hmRpos
  have hgp_le_g : gp ≤ g := (div_le_iff₀ hmRpos).2 (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hmR1 hg.le)
  have hgp1 : gp ≤ 1 := hgp_le_g.trans hg1
  have hrecip : 1 / gp = (m : ℝ) / g := by
    dsimp only [gp]
    field_simp [hg.ne', hmRpos.ne']
  have hu : 1 + log (1 / gp) = u := by
    rw [hrecip, log_div hmRpos.ne' hg.ne']
    dsimp only [u]
    rw [one_div, log_inv]
    ring
  have hCtail : 0 < Ctail := by dsimp only [Ctail]; positivity
  have hCaug : 0 < Caug := mul_pos hCtail (exp_pos _)
  have haug := scalar_tail_bound A u gp ell Caug (1 / 8) (1 / 1000000) 1
    hu.le hgp hgp1 hAu hCaug (by norm_num) (by norm_num) (by norm_num) hAM
  have harg : -(1 / 8 : ℝ) * ((ell : ℝ) - gp) =
      -((ell : ℝ) - gp) / 8 := by ring
  rw [harg, rpow_one] at haug
  have hshift : g - gp ≤ 1 := by linarith [hgp.le]
  have hcompare : Ctail * exp (-((ell : ℝ) - g) / 8) ≤
      Caug * exp (-((ell : ℝ) - gp) / 8) := by
    calc
      Ctail * exp (-((ell : ℝ) - g) / 8) ≤
          Ctail * exp ((1 / 8 : ℝ) + -((ell : ℝ) - gp) / 8) :=
        mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith)) hCtail.le
      _ = Caug * exp (-((ell : ℝ) - gp) / 8) := by
        dsimp only [Caug]
        rw [exp_add]
        ring
  refine ⟨hell, hmD, hm.trans hmD, hlower, hupper, hscale, hcount, hlogD, ?_, ?_⟩
  · intro R hR hRup
    apply htrade R hR
    simpa only [show (2 : ℝ) * 4 = 8 by norm_num] using hRup
  · calc
      Ctail * exp (-((ell : ℝ) - g) / 8) ≤
          Caug * exp (-((ell : ℝ) - gp) / 8) := hcompare
      _ ≤ (1 / 1000000 : ℝ) * gp := haug
      _ = g / (1000000 * (m : ℝ)) := by
        dsimp only [gp]
        rw [div_mul_div_comm, one_mul]
end Real
end

section

namespace TNLean.MPS.AreaLaw

/-- Increasing only the numerical count base absorbs the same physical
collar cost into the joint square budget. The physical dimension remains
`q`. Supporting the entropy schedule in ALVV, arXiv:1602.08828v2,
`thm:al-dg`, lines 1048–1099. -/
theorem collar_card_le_square_of_larger_count_base
    (q m ell d n : ℕ) (hq : 2 ≤ q) (hqm : q ≤ m) (hell : 1 ≤ ell)
    (hd : d ≤ 2 * ell)
    (hn : n ≤ ((q * ell ^ 2) ^ (18 * ell + 2 * (ell ^ 2 / ell))) ^ 2) :
    n * q ^ (2 * d) ≤ ((m * ell ^ 2) ^ (22 * ell)) ^ 2 := by
  exact (collar_card_le_square_at_square_degree q ell d n hq hell hd hn).trans
    (Nat.pow_le_pow_left
      (Nat.pow_le_pow_left (Nat.mul_le_mul_right (ell ^ 2) hqm) (22 * ell)) 2)
end TNLean.MPS.AreaLaw
end

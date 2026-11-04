/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Independent truncation and polynomial scales

The norm bound `3*t + 4*ell` permits an independent choice of the hard
truncation threshold and the polynomial window length. The scalar estimates
below retain both scales in the Chebyshev exponent. They support ALVV,
arXiv:1602.08828v2, Corollary 4.6 (`c:goodagsphardtrunc`) and the approximation
conclusion of Theorem 4.9 (`thm:al-dg`). They do not assert that the physical
approximating vectors or matrix product representations have been constructed.

**Local fix (parameter choice):** The printed prescription in the proof of
Theorem 4.9 does not give the stated accuracy uniformly in the gap. Independent
threshold and window choices are justified in
`docs/paper-gaps/alvv16_approximation_parameters.tex`; the theorem itself is
not refuted by that calculation.
-/

namespace Real

/-- A fourth-power lower bound gives the required Chebyshev exponent when
both the truncation-dominated and window-dominated regimes are allowed.
The independent scales enter through the physical norm budget `3*t + 4*ell`.
Auxiliary to ALVV, arXiv:1602.08828v2, Corollary 4.6, item 1. -/
theorem independent_truncation_filter_exponent
    (ell t g a R : ℝ) (hell : 0 ≤ ell) (ha : 0 ≤ a) (hat : a ≤ t)
    (hbase : 7 ≤ ell * g) (hfourth : 7 * t * a ^ 2 ≤ g * ell ^ 4)
    (hR : 0 < R) (hRbudget : R ≤ 3 * t + 4 * ell) :
    a ≤ ell ^ 2 * sqrt (g / R) := by
  have hpoly : a ^ 2 * R ≤ g * ell ^ 4 := by
    rcases le_total t ell with htell | hellt
    · have haell : a ≤ ell := hat.trans htell
      have hsq : a ^ 2 ≤ ell ^ 2 := by nlinarith
      have hRell : R ≤ 7 * ell := by linarith only [hRbudget, htell]
      calc
        a ^ 2 * R ≤ a ^ 2 * (7 * ell) :=
          mul_le_mul_of_nonneg_left hRell (sq_nonneg a)
        _ ≤ 7 * ell ^ 3 := by nlinarith [mul_le_mul_of_nonneg_right hsq hell]
        _ ≤ g * ell ^ 4 := by
          nlinarith [mul_le_mul_of_nonneg_right hbase (pow_nonneg hell 3)]
    · have hRt : R ≤ 7 * t := by linarith only [hRbudget, hellt]
      exact (mul_le_mul_of_nonneg_left hRt (sq_nonneg a)).trans
        (by nlinarith only [hfourth])
  have hg : 0 ≤ g := by nlinarith only [hbase, hell]
  have hsqrt := sq_sqrt (div_nonneg hg hR.le)
  apply (sq_le_sq₀ ha (mul_nonneg (sq_nonneg ell) (sqrt_nonneg _))).mp
  calc
    a ^ 2 ≤ g * ell ^ 4 / R := (le_div_iff₀ hR).2 hpoly
    _ = (ell ^ 2 * sqrt (g / R)) ^ 2 := by rw [mul_pow, hsqrt]; ring

/-- An integer window length can be chosen with a fourth-root dependence on
`t*a^2/g`, while the norm budget continues to use the independent threshold.
The constants are uniform in all positive gaps at most one.
Auxiliary to ALVV, arXiv:1602.08828v2, Corollary 4.6 and Theorem 4.9. -/
theorem exists_independent_truncation_filter_scale
    (t g a : ℝ) (hg : 0 < g) (hg1 : g ≤ 1) (ha : 0 ≤ a) (hat : a ≤ t) :
    ∃ ell : ℕ, 1 ≤ ell ∧
      (ell : ℝ) ≤ 8 / g + (7 * t * a ^ 2 / g) ^ (1 / 4 : ℝ) ∧
      ∀ R : ℝ, 0 < R → R ≤ 3 * t + 4 * (ell : ℝ) →
        a ≤ (ell : ℝ) ^ 2 * sqrt (g / R) := by
  let b : ℝ := (7 * t * a ^ 2 / g) ^ (1 / 4 : ℝ)
  let ell : ℕ := ⌈7 / g + b⌉₊
  have ht : 0 ≤ t := ha.trans hat
  have hb : 0 ≤ b := rpow_nonneg (by positivity) _
  have hb4 : b ^ 4 = 7 * t * a ^ 2 / g := by
    simpa only [b, Nat.cast_ofNat, one_div] using
      rpow_inv_natCast_pow (by positivity : 0 ≤ 7 * t * a ^ 2 / g) (by decide : 4 ≠ 0)
  have hlower : 7 / g + b ≤ (ell : ℝ) := Nat.le_ceil _
  have hseven : 7 ≤ (ell : ℝ) * g := by
    apply (div_le_iff₀ hg).mp
    linarith only [hlower, hb]
  have hell1 : 1 ≤ ell := by
    have : 1 ≤ (ell : ℝ) := by nlinarith [(Nat.cast_nonneg ell : (0 : ℝ) ≤ (ell : ℝ))]
    exact_mod_cast this
  have hbell : b ≤ (ell : ℝ) := by
    linarith only [hlower, div_nonneg (by norm_num : (0 : ℝ) ≤ 7) hg.le]
  have hfourth : 7 * t * a ^ 2 ≤ g * (ell : ℝ) ^ 4 := by
    have hpow := pow_le_pow_left₀ hb hbell 4
    rw [hb4] at hpow
    have := (div_le_iff₀ hg).mp hpow
    nlinarith only [this]
  have hceil : (ell : ℝ) ≤ 7 / g + b + 1 :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ 7 / g + b)).le
  have hinv : 1 ≤ 1 / g := (le_div_iff₀ hg).2 (by simpa only [one_mul] using hg1)
  refine ⟨ell, hell1, ?_, ?_⟩
  · change (ell : ℝ) ≤ 8 / g + b
    have hsplit : 8 / g = 7 / g + 1 / g := by ring
    rw [hsplit]
    linarith only [hceil, hinv]
  · intro R hR hRbudget
    exact independent_truncation_filter_exponent (ell : ℝ) t g a R
      (Nat.cast_nonneg ell) ha hat hseven hfourth hR hRbudget

/-- A threshold linear in the required logarithmic accuracy admits an integer
window bound with the gap power `1/4` and accuracy power `3/4`. The additional
inverse-gap term controls the regime in which the window exceeds the threshold.
Auxiliary to ALVV, arXiv:1602.08828v2, Theorem 4.9, proof after
Proposition 4.10 (`local_alg_arxiv_v2.tex`, line 1080). -/
theorem exists_quarter_power_truncation_filter_scale
    (C g a : ℝ) (hC : 1 ≤ C) (hg : 0 < g) (hg1 : g ≤ 1) (ha : 0 ≤ a) :
    ∃ ell : ℕ, 1 ≤ ell ∧
      (ell : ℝ) ≤ 8 / g +
        (7 * C) ^ (1 / 4 : ℝ) * (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) ∧
      ∀ R : ℝ, 0 < R → R ≤ 3 * (C * a) + 4 * (ell : ℝ) →
        a ≤ (ell : ℝ) ^ 2 * sqrt (g / R) := by
  obtain ⟨ell, hell, hbound, hfilter⟩ :=
    exists_independent_truncation_filter_scale (C * a) g a hg hg1 ha (by nlinarith)
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hroot : (7 * (C * a) * a ^ 2 / g) ^ (1 / 4 : ℝ) =
      (7 * C) ^ (1 / 4 : ℝ) * (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) := by
    have hbase : 7 * (C * a) * a ^ 2 / g = ((7 * C) * (1 / g)) * a ^ 3 := by ring
    have hpow : (a ^ 3) ^ (1 / 4 : ℝ) = a ^ (3 / 4 : ℝ) := by
      rw [← rpow_natCast a 3, ← rpow_mul ha]
      norm_num
    rw [hbase, mul_rpow (by positivity) (pow_nonneg ha 3),
      mul_rpow (by positivity) (by positivity), hpow]
  exact ⟨ell, hell, hroot ▸ hbound, hfilter⟩

/-- One universal threshold constant makes the actual three-bulk residual
smaller than every prescribed projection scale times the normalized gap.
Both logarithms are retained. Auxiliary to ALVV, arXiv:1602.08828v2,
Corollary 4.6 and the approximation proof of Theorem 4.9, line 1080. -/
theorem exists_independent_truncation_threshold_constant :
    ∃ C : ℝ, 21 ≤ C ∧
      ∀ g tau : ℝ, 0 < g → g ≤ 1 → 0 < tau → tau ≤ 1 →
      let u := 1 + log (1 / g) + log (1 / tau)
      21 ≤ C * u ∧
        (288 * exp (11 / 8)) * exp (-(C * u - g) / 8) ≤ tau * g / 1000000 := by
  let K : ℝ := 288 * exp (11 / 8) * 1000000
  have hK : 1 ≤ K := by
    have he : 1 ≤ exp (11 / 8 : ℝ) := (one_le_exp_iff).2 (by norm_num)
    dsimp only [K]
    nlinarith only [he]
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hlogK : 0 ≤ log K := log_nonneg hK
  let C : ℝ := 32 + 8 * log K
  have hC : 21 ≤ C := by dsimp only [C]; linarith only [hlogK]
  refine ⟨C, hC, ?_⟩
  intro g tau hg hg1 htau htau1 u
  have hlogg : 0 ≤ log (1 / g) := log_nonneg ((one_le_div hg).2 hg1)
  have hlogtau : 0 ≤ log (1 / tau) := log_nonneg ((one_le_div htau).2 htau1)
  have hu : 1 ≤ u := by dsimp only [u]; linarith only [hlogg, hlogtau]
  have hCu : C ≤ C * u := le_mul_of_one_le_right (by linarith only [hC]) hu
  refine ⟨hC.trans hCu, ?_⟩
  have hratio : log (K / (tau * g)) = log K + log (1 / g) + log (1 / tau) := by
    rw [log_div hKpos.ne' (mul_pos htau hg).ne', log_mul htau.ne' hg.ne']
    simp only [one_div, log_inv]
    ring
  have hmul : log K ≤ log K * u := le_mul_of_one_le_right hlogK hu
  have harg : -(C * u - g) / 8 ≤ -log (K / (tau * g)) := by
    rw [hratio]
    have huEq : u = 1 + log (1 / g) + log (1 / tau) := rfl
    dsimp only [C]
    nlinarith only [hmul, hu, huEq, hg1]
  calc
    _ ≤ (288 * exp (11 / 8)) * exp (-log (K / (tau * g))) :=
      mul_le_mul_of_nonneg_left (exp_le_exp.mpr harg) (by positivity)
    _ = tau * g / 1000000 := by
      rw [exp_neg, exp_log (div_pos hKpos (mul_pos htau hg))]
      dsimp only [K]
      field_simp

end Real

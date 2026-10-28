/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Huang.FilterParameters
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Uniform logarithmic bounds for the Gaussian-filter parameters

All constants are chosen before the chain length. Inverse precision grows at most
linearly, while the spectral scale, time cutoff and propagation exponent grow at most
logarithmically. These conservative estimates support Huang, arXiv:1406.6355v6,
Section 5.4, Lemmas 18--19, without claiming the printed sharper gap dependence.
-/

namespace TNLean.MPS.AreaLaw

/-- Uniform linear and logarithmic parameter bounds with constants before chain length.
Supporting estimates for Huang, Section 5.4, equations (19)--(22). -/
theorem exists_huangFilter_log_bounds {c Delta : ℝ} (hc : 0 < c) (hDelta : 0 < Delta) :
    ∃ K A B : ℝ, 1 ≤ K ∧ 0 < A ∧ 0 < B ∧ ∀ L : ℕ,
      1 / huangFilterEta c L ≤ K * ((L : ℝ) + 1) ∧
      Real.log (1 / huangFilterEta c L) ≤ Real.log K + Real.log ((L : ℝ) + 1) ∧
      huangFilterScale c L + 1 ≤ A * (Real.log ((L : ℝ) + 1) + 1) ∧
      huangFilterTime c Delta L ≤ B * (Real.log ((L : ℝ) + 1) + 1) := by
  let K := 64 * (c + 1) / c
  have hK : 1 ≤ K := by
    dsimp only [K]
    rw [le_div_iff₀ hc]
    linarith
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  let A := 8 * Real.log K + 9
  let B := A / Delta ^ 2 + Real.log 2 + Real.log K + 2
  have hA : 0 < A := by dsimp only [A]; linarith
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨K, A, B, hK, hA, hB, ?_⟩
  intro L
  have hL : 0 ≤ (L : ℝ) := Nat.cast_nonneg L
  have hL1 : 0 < (L : ℝ) + 1 := by positivity
  have hlogL : 0 ≤ Real.log ((L : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hη := huangFilterEta_bounds hc L
  have hinv : 1 / huangFilterEta c L ≤ K * ((L : ℝ) + 1) := by
    dsimp only [huangFilterEta, K]
    rw [one_div_div]
    calc
      _ ≤ 64 * ((c + 1) * ((L : ℝ) + 1)) / c := by
        apply div_le_div_of_nonneg_right _ hc.le
        nlinarith [mul_nonneg hc.le hL]
      _ = _ := by ring
  have hlog : Real.log (1 / huangFilterEta c L) ≤
      Real.log K + Real.log ((L : ℝ) + 1) := by
    calc
      _ ≤ Real.log (K * ((L : ℝ) + 1)) := Real.log_le_log (one_div_pos.mpr hη.1) hinv
      _ = _ := Real.log_mul hKpos.ne' hL1.ne'
  have hscale : huangFilterScale c L + 1 ≤ A * (Real.log ((L : ℝ) + 1) + 1) := by
    dsimp only [huangFilterScale, A]
    nlinarith [mul_nonneg hlogK hlogL]
  have hlogtime : Real.log (2 / huangFilterEta c L) ≤
      Real.log 2 + Real.log K + Real.log ((L : ℝ) + 1) := by
    calc
      _ = Real.log 2 + Real.log (1 / huangFilterEta c L) := by
        rw [show 2 / huangFilterEta c L = 2 * (1 / huangFilterEta c L) by ring]
        exact Real.log_mul (by norm_num) (one_div_pos.mpr hη.1).ne'
      _ ≤ _ := by linarith
  have htime : huangFilterTime c Delta L ≤ B * (Real.log ((L : ℝ) + 1) + 1) := by
    rw [huangFilterTime, huangFilterVariance_coe hc]
    calc
      _ ≤ A * (Real.log ((L : ℝ) + 1) + 1) / Delta ^ 2 +
          (Real.log 2 + Real.log K + Real.log ((L : ℝ) + 1)) + 1 := by
        gcongr
        linarith only [hscale]
      _ = (A / Delta ^ 2) * (Real.log ((L : ℝ) + 1) + 1) +
          (Real.log 2 + Real.log K + Real.log ((L : ℝ) + 1)) + 1 := by ring
      _ ≤ _ := by
        dsimp only [B]
        nlinarith [mul_nonneg (by linarith : 0 ≤ Real.log 2 + Real.log K + 1) hlogL]
  exact ⟨hinv, hlog, hscale, htime⟩

/-- The exponent of the simultaneous cut-rank bound is logarithmic in length with a
constant chosen first. Supporting estimate for Huang, Section 5.4, Lemma 19. -/
theorem exists_huangFilter_radius_log_bound {c Delta : ℝ}
    (hc : 0 < c) (hDelta : 0 < Delta) :
    ∃ B : ℝ, 0 < B ∧ ∀ L : ℕ,
      ((8 * chainPropagationRadius L (huangFilterTime c Delta L) (huangFilterEta c L) + 8 : ℕ)
        : ℝ) ≤ B * (Real.log ((L : ℝ) + 1) + 1) := by
  obtain ⟨K, A, B, hK, _, hB, hparams⟩ := exists_huangFilter_log_bounds hc hDelta
  have hv : 0 ≤ chainGridLRVelocity + 1 := by unfold chainGridLRVelocity; positivity
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  let D := 16 * ((chainGridLRVelocity + 1) * B +
    |Real.log chainGridLRPrefactor| + Real.log K + 3)
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro L
  have hη := huangFilterEta_bounds hc L
  have htime := (hparams L).2.2.2
  have hlog := (hparams L).2.1
  have hlogL : 0 ≤ Real.log ((L : ℝ) + 1) :=
    Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg L))
  have hwidth := chainPropagationRadius_width_le L
    (huangFilterTime_pos hc hDelta L).le hη.1
  rw [min_eq_left (by linarith [hη.2] : huangFilterEta c L ≤ 1)] at hwidth
  have hscaled := mul_le_mul_of_nonneg_left htime hv
  have hlogscaled : Real.log (1 / huangFilterEta c L) ≤
      (Real.log K + 1) * (Real.log ((L : ℝ) + 1) + 1) := by
    nlinarith [mul_nonneg hlogK hlogL]
  have hCscaled : |Real.log chainGridLRPrefactor| ≤
      |Real.log chainGridLRPrefactor| * (Real.log ((L : ℝ) + 1) + 1) := by
    nlinarith [mul_nonneg (abs_nonneg (Real.log chainGridLRPrefactor)) hlogL]
  dsimp only [D]
  push_cast at hwidth ⊢
  nlinarith only [hwidth, hscaled, hlogscaled, hCscaled, hlogL]

/-- A natural-degree polynomial bounds the exponential of the logarithmic radius.
The degree and coefficient depend only on fixed `q`, `Delta` and `c`, before length.
Supporting estimate for Huang, Section 5.4, Lemma 19. -/
theorem exists_huangFilter_bond_polynomial {q : ℕ} (hq : 1 ≤ q) {c Delta : ℝ}
    (hc : 0 < c) (hDelta : 0 < Delta) :
    ∃ d : ℕ, ∀ L : ℕ,
      ((q ^ (8 * chainPropagationRadius L (huangFilterTime c Delta L)
        (huangFilterEta c L) + 8) : ℕ) : ℝ) ≤
      Real.exp d * ((L : ℝ) + 1) ^ d := by
  obtain ⟨B, hB, hbound⟩ := exists_huangFilter_radius_log_bound hc hDelta
  have hqreal : 1 ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : 0 < (q : ℝ) := lt_of_lt_of_le (by norm_num) hqreal
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hqreal
  let d : ℕ := ⌈B * Real.log q⌉₊
  have hd : B * Real.log q ≤ (d : ℝ) := Nat.le_ceil _
  refine ⟨d, ?_⟩
  intro L
  let n := 8 * chainPropagationRadius L (huangFilterTime c Delta L) (huangFilterEta c L) + 8
  have hlogL : 0 ≤ Real.log ((L : ℝ) + 1) :=
    Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg L))
  have hexponent : (n : ℝ) * Real.log q ≤
      (d : ℝ) * (Real.log ((L : ℝ) + 1) + 1) := by
    have h1 := mul_le_mul_of_nonneg_right (hbound L) hlogq
    have h2 := mul_le_mul_of_nonneg_right hd (by positivity :
      0 ≤ Real.log ((L : ℝ) + 1) + 1)
    nlinarith only [h1, h2]
  calc
    _ = Real.exp ((n : ℝ) * Real.log q) := by
      rw [Real.exp_nat_mul, Real.exp_log hqpos, Nat.cast_pow]
    _ ≤ Real.exp ((d : ℝ) * (Real.log ((L : ℝ) + 1) + 1)) :=
      Real.exp_le_exp.mpr hexponent
    _ = Real.exp d * ((L : ℝ) + 1) ^ d := by
      rw [mul_add, mul_one, Real.exp_add, Real.exp_nat_mul,
        Real.exp_log (by positivity : 0 < (L : ℝ) + 1)]
      ring

end TNLean.MPS.AreaLaw

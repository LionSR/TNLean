/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Huang.GridLocalization
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Buffer radii at prescribed propagation error

The radius absorbs the chain-length factor and elapsed time in the derived propagation
error. Its width is bounded explicitly by a linear function of the time cutoff and the
logarithms of length and inverse precision. These scalar estimates support Osborne,
arXiv:quant-ph/0508031v2, equations (12)--(13), and Huang,
arXiv:1406.6355v6, Section 5.4, Lemma 19.
-/

namespace TNLean.MPS.AreaLaw

/-- An integer buffer radius chosen before all sample times in a fixed cutoff interval.
Osborne, equations (12)--(13); Huang, Section 5.4, Lemma 19. -/
noncomputable def chainPropagationRadius (L : ℕ) (T epsilon : ℝ) : ℕ :=
  ⌈2 * (chainGridLRVelocity * T +
    Real.log (((L : ℝ) + 1) * chainGridLRPrefactor * (T + 1) / min epsilon 1))⌉₊

/-- The explicit radius makes the full propagation error at most the requested precision.
Osborne, arXiv:quant-ph/0508031v2, equations (12)--(13). -/
theorem chainPropagationRadius_error_le (L n : ℕ) (hn : n ≤ L) {T epsilon : ℝ}
    (hT : 0 ≤ T) (hepsilon : 0 < epsilon) :
    (n : ℝ) * chainGridLRPrefactor *
      Real.exp (chainGridLRVelocity * T - (chainPropagationRadius L T epsilon : ℝ) / 2) * T ≤
        epsilon := by
  let delta := min epsilon 1
  let alpha := ((L : ℝ) + 1) * chainGridLRPrefactor * (T + 1) / delta
  have hdelta : 0 < delta := lt_min hepsilon (by norm_num)
  have hC := chainGridLRPrefactor_pos
  have halpha : 0 < alpha := by dsimp only [alpha]; positivity
  have hr : 2 * (chainGridLRVelocity * T + Real.log alpha) ≤
      (chainPropagationRadius L T epsilon : ℝ) := Nat.le_ceil _
  have hexp : Real.exp (chainGridLRVelocity * T -
      (chainPropagationRadius L T epsilon : ℝ) / 2) ≤ 1 / alpha := by
    calc
      _ ≤ Real.exp (-Real.log alpha) := Real.exp_le_exp.mpr (by linarith only [hr])
      _ = 1 / alpha := by simp only [Real.exp_neg, Real.exp_log halpha, one_div]
  have hcount : (n : ℝ) ≤ (L : ℝ) + 1 := by exact_mod_cast (hn.trans (Nat.le_succ L))
  have hcancel : delta * alpha = ((L : ℝ) + 1) * chainGridLRPrefactor * (T + 1) := by
    dsimp only [alpha]
    field_simp
  have hprod : (n : ℝ) * chainGridLRPrefactor * T ≤ delta * alpha := by
    rw [hcancel]
    calc
      _ ≤ (((L : ℝ) + 1) * chainGridLRPrefactor) * T :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcount hC.le) hT
      _ ≤ (((L : ℝ) + 1) * chainGridLRPrefactor) * (T + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  calc
    _ = ((n : ℝ) * chainGridLRPrefactor * T) *
        Real.exp (chainGridLRVelocity * T - (chainPropagationRadius L T epsilon : ℝ) / 2) := by ring
    _ ≤ ((n : ℝ) * chainGridLRPrefactor * T) * (1 / alpha) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = ((n : ℝ) * chainGridLRPrefactor * T) / alpha := by
      simp only [div_eq_mul_inv, one_mul]
    _ ≤ delta := (div_le_iff₀ halpha).mpr hprod
    _ ≤ epsilon := min_le_left _ _

/-- The constructed grid width is linear in time and logarithmic in length and inverse
precision, with universal constants. Osborne, equations (12)--(13); Huang, Lemma 19. -/
theorem chainPropagationRadius_width_le (L : ℕ) {T epsilon : ℝ}
    (hT : 0 ≤ T) (hepsilon : 0 < epsilon) :
    ((2 * chainPropagationRadius L T epsilon + 2 : ℕ) : ℝ) ≤
      4 * ((chainGridLRVelocity + 1) * T + Real.log ((L : ℝ) + 1) +
        |Real.log chainGridLRPrefactor| + Real.log (1 / min epsilon 1)) + 4 := by
  let delta := min epsilon 1
  let alpha := ((L : ℝ) + 1) * chainGridLRPrefactor * (T + 1) / delta
  let x := chainGridLRVelocity * T + Real.log alpha
  let R := (chainGridLRVelocity + 1) * T + Real.log ((L : ℝ) + 1) +
    |Real.log chainGridLRPrefactor| + Real.log (1 / delta)
  have hdelta : 0 < delta := lt_min hepsilon (by norm_num)
  have hC := chainGridLRPrefactor_pos
  have hL : 0 < (L : ℝ) + 1 := by positivity
  have hT1 : 0 < T + 1 := by linarith
  have hv : 0 ≤ chainGridLRVelocity := by unfold chainGridLRVelocity; positivity
  have hlogL : 0 ≤ Real.log ((L : ℝ) + 1) :=
    Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg L))
  have hlogdelta : 0 ≤ Real.log (1 / delta) :=
    Real.log_nonneg ((one_le_div hdelta).mpr (min_le_right epsilon 1))
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hlogalpha : Real.log alpha = Real.log ((L : ℝ) + 1) +
      Real.log chainGridLRPrefactor + Real.log (T + 1) + Real.log (1 / delta) := by
    dsimp only [alpha]
    rw [Real.log_div (mul_ne_zero (mul_ne_zero hL.ne' hC.ne') hT1.ne') hdelta.ne',
      Real.log_mul (mul_ne_zero hL.ne' hC.ne') hT1.ne', Real.log_mul hL.ne' hC.ne',
      Real.log_div one_ne_zero hdelta.ne', Real.log_one]
    ring
  have hlogT : Real.log (T + 1) ≤ T := by
    simpa only [add_sub_cancel_right] using Real.log_le_sub_one_of_pos hT1
  have hxR : x ≤ R := by
    dsimp only [x, R]
    rw [hlogalpha]
    nlinarith [le_abs_self (Real.log chainGridLRPrefactor)]
  have hmax : max 0 x ≤ R := max_le hR hxR
  have hceil : (chainPropagationRadius L T epsilon : ℝ) ≤ 2 * max 0 x + 1 := by
    have hmono : chainPropagationRadius L T epsilon ≤ ⌈2 * max 0 x⌉₊ :=
      Nat.ceil_mono (mul_le_mul_of_nonneg_left (le_max_right 0 x) (by norm_num))
    have hmonoR : (chainPropagationRadius L T epsilon : ℝ) ≤ (⌈2 * max 0 x⌉₊ : ℝ) := by
      exact_mod_cast hmono
    exact hmonoR.trans (Nat.ceil_lt_add_one (by positivity : 0 ≤ 2 * max 0 x)).le
  change ((2 * chainPropagationRadius L T epsilon + 2 : ℕ) : ℝ) ≤ 4 * R + 4
  push_cast
  nlinarith only [hceil, hmax]

end TNLean.MPS.AreaLaw

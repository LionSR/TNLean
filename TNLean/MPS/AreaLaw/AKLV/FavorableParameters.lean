/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PolynomialFilterParameters
import Mathlib.Data.Nat.Sqrt

/-!
# Favorable scalar parameters for the AKLV filter

One universal constant chooses the window scale and square degree. The actual
AKLV polynomial rank budget and squared Chebyshev shrinking coefficient then
satisfy a favorable tradeoff, with an explicit cubic logarithmic rank bound.
The proof specializes the already established joint scalar parameter theorem;
it does not reconstruct its logarithmic absorption or ceiling estimates.

Source: AKLV, arXiv:1301.1162v1, Section 6.1, the parameter choice following
Theorem `thm:Ht` and the proof of Lemma `l:5`, lines 1016--1048.
This is a scalar auxiliary. It asserts no physical filter, available chain
window, approximation sequence, or entropy conclusion.
-/

namespace Real

/-- A uniform scalar choice makes the square-degree AKLV rank budget and
squared shrinking coefficient favorable. The logarithms of the inverse gap
remain explicit in `u`. This supports AKLV, arXiv:1301.1162v1, Section 6.1,
lines 1016--1048; applying it to a physical filter is a separate step. -/
theorem exists_aklv_favorable_scalar_parameters :
    ∃ A : ℝ, 1 ≤ A ∧ 21 ≤ A ∧
      ∀ (q : ℕ) (g : ℝ), 2 ≤ q → 0 < g → g ≤ 1 →
      let u := 1 + log (q : ℝ) + log (1 / g)
      let s : ℕ := ⌈A * u ^ 2 / g⌉₊
      let ell := s ^ 2
      let t0 := 1024 + 16 * log (1 / g)
      let R := 2 * t0 + (s : ℝ)
      let D := (q * (s ^ 2 + 1)) ^ (32 * (2 * s + 1))
      let Daux := (q * s ^ 2) ^ (22 * s)
      let delta := 4 * exp (-(4 * (ell : ℝ) * sqrt ((9 * g / 10) / R)))
      A * u ^ 2 / g ≤ (s : ℝ) ∧ (s : ℝ) ≤ (A + 1) * u ^ 2 / g ∧
      21 ≤ s ∧ log (1 / g) ≤ (s : ℝ) ∧
      ell / s = s ∧ Nat.sqrt ell = s ∧
      0 < R ∧ R ≤ 2081 * (s : ℝ) ∧
      D ≤ Daux ^ 9 ∧ 0 < delta ∧
      (D : ℝ) * delta ≤ 1 / 100000 ∧ (D : ℝ) * delta < 1 / 256 ∧
      log (D : ℝ) ≤ 198 * (A + 1) * (6 + 2 * log (A + 1)) / g * u ^ 3 := by
  obtain ⟨A, hA, hA21, _hAM, _hAlog, hall⟩ :=
    exists_dg_scalar_parameters (2081 / 2) 0 (by norm_num)
  refine ⟨A, hA, hA21, ?_⟩
  intro q g hq hg hg1 u s ell t0 R D Daux delta
  obtain ⟨hsLower, hsUpper, hsA, _hcount, hlogDaux, htrade, _htail⟩ := hall q g hq hg hg1
  have hs21R : (21 : ℝ) ≤ (s : ℝ) := hA21.trans hsA
  have hs21 : 21 ≤ s := by exact_mod_cast hs21R
  have hspos : 0 < s := by omega
  have hb : 0 ≤ log (1 / g) := log_nonneg ((one_le_div hg).mpr hg1)
  have hlogq : 0 ≤ log (q : ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
  have hu : 1 + log (1 / g) ≤ u := by dsimp only [u]; linarith
  have hsb : log (1 / g) ≤ (s : ℝ) := by
    calc
      log (1 / g) ≤ u ^ 2 := by nlinarith only [hu, hb, sq_nonneg (u - 1)]
      _ ≤ A * u ^ 2 / g := (le_div_iff₀ hg).mpr
        (by nlinarith only [mul_le_mul_of_nonneg_right (hg1.trans hA) (sq_nonneg u)])
      _ ≤ (s : ℝ) := hsLower
  have hR : 0 < R := by dsimp only [R, t0]; linarith
  have hRup : R ≤ 2081 * (s : ℝ) := by dsimp only [R, t0]; linarith
  have hsquare : 1 ≤ s ^ 2 := one_le_pow₀ (by omega : 1 ≤ s)
  have hbaseAux : 2 ≤ q * s ^ 2 := by
    nlinarith only [Nat.mul_le_mul_left q hsquare, hq]
  have hbase : q * (s ^ 2 + 1) ≤ (q * s ^ 2) ^ 2 := by
    calc
      _ ≤ 2 * (q * s ^ 2) := by nlinarith only [Nat.mul_le_mul_left q hsquare]
      _ ≤ (q * s ^ 2) ^ 2 := by
        nlinarith only [Nat.mul_le_mul_left (q * s ^ 2) hbaseAux]
  have hD : D ≤ Daux ^ 9 := by
    calc
      D ≤ ((q * s ^ 2) ^ 2) ^ (32 * (2 * s + 1)) := Nat.pow_le_pow_left hbase _
      _ = (q * s ^ 2) ^ (64 * (2 * s + 1)) := by rw [← pow_mul]; congr 1; omega
      _ ≤ (q * s ^ 2) ^ (198 * s) := Nat.pow_le_pow_right (by omega) (by omega)
      _ = Daux ^ 9 := by dsimp only [Daux]; rw [← pow_mul]; congr 1; omega
  have hDaux1 : 1 ≤ Daux := one_le_pow₀ (by omega : 1 ≤ q * s ^ 2)
  have hDpos : 0 < (D : ℝ) := by
    exact_mod_cast (Nat.pow_pos (by nlinarith only [hq, hsquare] : 0 < q * (s ^ 2 + 1)))
  have hDauxR : 1 ≤ (Daux : ℝ) := by exact_mod_cast hDaux1
  have hDpow : (D : ℝ) ≤ (Daux : ℝ) ^ 12 := by
    calc
      (D : ℝ) ≤ (Daux : ℝ) ^ 9 := by exact_mod_cast hD
      _ ≤ (Daux : ℝ) ^ 12 := pow_le_pow_right₀ hDauxR (by norm_num)
  let deltaAux := 4 * exp (-(4 * (s : ℝ) ^ 2 * sqrt ((4 * g / 5) / R)))
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  have hdeltaLe : delta ≤ deltaAux := by
    dsimp only [delta, deltaAux, ell]
    push_cast
    apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by norm_num)
    apply neg_le_neg_iff.mpr
    apply mul_le_mul_of_nonneg_left (sqrt_le_sqrt ?_) (by positivity)
    exact div_le_div_of_nonneg_right (by linarith) hR.le
  have htradeAux : (Daux : ℝ) ^ 12 * deltaAux ≤ 1 / 100000 := by
    apply htrade R hR
    nlinarith only [hRup]
  have hfinal : (D : ℝ) * delta ≤ 1 / 100000 :=
    (mul_le_mul hDpow hdeltaLe hdelta.le (by positivity)).trans htradeAux
  have hlogD : log (D : ℝ) ≤ 9 * log (Daux : ℝ) := by
    calc
      log (D : ℝ) ≤ log ((Daux : ℝ) ^ 9) := log_le_log hDpos (by exact_mod_cast hD)
      _ = 9 * log (Daux : ℝ) := by rw [log_pow]; norm_num
  refine ⟨hsLower, hsUpper, hs21, hsb, ?_, ?_, hR, hRup, hD, hdelta,
    hfinal, hfinal.trans_lt (by norm_num), ?_⟩
  · dsimp only [ell]
    rw [pow_two, Nat.mul_div_cancel s hspos]
  · exact Nat.sqrt_eq' s
  · calc
      log (D : ℝ) ≤ 9 * log (Daux : ℝ) := hlogD
      _ ≤ 9 * (22 * (A + 1) * (6 + 2 * log (A + 1)) / g * u ^ 3) :=
        mul_le_mul_of_nonneg_left hlogDaux (by norm_num)
      _ = _ := by ring

end Real

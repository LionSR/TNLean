/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.FavorableParameters

/-!
# Favorable scalar parameters for frustration-free exterior clipping

The existing favorable scalar theorem, applied at a fixed smaller gap, gives
parameters for the actual frustration-free cutoff `1024/g` and preserved gap
`g/2`. The window and logarithmic rank costs retain the inverse-gap logarithm.
No logarithmic absorption proof is duplicated.

Source: AKLV, arXiv:1301.1162v1, Section 4, proof of `t:ent`,
`1dfrustrated34.tex`, lines 810–846. This scalar auxiliary retains
`1 + log q + log(1/g)` rather than claiming the printed sharper rate with all
inverse-gap logarithms removed. It constructs neither a physical filter nor
an available chain window; those are separate applications.

**Scope restriction (rate):** The cost is proportional to
`(1 + log q + log(1/g))³/g`, retaining inverse-gap logarithms rather than
formalizing the printed `log³ q/g` rate. This restriction is recorded in
`docs/paper-gaps/aklv13_two_block_robustness.tex`.
-/

namespace Real

/-- One universal scalar choice gives a favorable tradeoff for the exact
frustration-free clipping cutoff and half-gap. The explicit window and rank
coefficients depend only on the universal `A`, before all physical parameters.

Source: AKLV, arXiv:1301.1162v1, proof of `t:ent`, lines 827–846, with the
inverse-gap logarithms retained. This specializes the existing scalar theorem
at `g/8192`; no actual first-excited-energy hypothesis is used. -/
lemma exists_aklv_frustrationFree_scalar_parameters :
    ∃ A : ℝ, 1 ≤ A ∧ 21 ≤ A ∧
      ∀ (q : ℕ) (g : ℝ), 2 ≤ q → 0 < g → g ≤ 1 →
      let g0 : ℝ := g / 8192
      let u : ℝ := 1 + log (q : ℝ) + log (1 / g)
      let u0 : ℝ := 1 + log (q : ℝ) + log (1 / g0)
      let s : ℕ := ⌈A * u0 ^ 2 / g0⌉₊
      let ell : ℕ := s ^ 2
      let t : ℝ := 1024 / g
      let R : ℝ := 2 * t + (s : ℝ)
      let D : ℕ := (q * (s ^ 2 + 1)) ^ (32 * (2 * s + 1))
      let delta : ℝ := 4 * exp (-(4 * (ell : ℝ) * sqrt ((g / 2) / R)))
      21 ≤ s ∧ 1 / g ≤ (s : ℝ) ∧
      (s : ℝ) ≤ 8192 * (A + 1) * (1 + log 8192) ^ 2 / g * u ^ 2 ∧
      ell / s = s ∧ Nat.sqrt ell = s ∧
      0 < R ∧ 0 < delta ∧
      (D : ℝ) * delta ≤ 1 / 100000 ∧ (D : ℝ) * delta < 1 / 256 ∧
      log (D : ℝ) ≤
        (8192 * (198 * (A + 1) * (6 + 2 * log (A + 1))) *
          (1 + log 8192) ^ 3) / g * u ^ 3 := by
  obtain ⟨A, hA, hA21, hscalar⟩ := exists_aklv_favorable_scalar_parameters
  refine ⟨A, hA, hA21, ?_⟩
  intro q g hq hg hg1 g0 u u0 s ell t R D delta
  have hg0 : 0 < g0 := by dsimp only [g0]; positivity
  have hg01 : g0 ≤ 1 := by dsimp only [g0]; linarith
  have hg0g : g0 ≤ g := by dsimp only [g0]; linarith
  let t0 := 1024 + 16 * log (1 / g0)
  let R0 := 2 * t0 + (s : ℝ)
  let delta0 := 4 * exp (-(4 * (ell : ℝ) * sqrt ((9 * g0 / 10) / R0)))
  obtain ⟨hsLower, hsUpper, hs21, _hslog, hdiv, hsqrt, hR0, _hR0up, _hDaux,
      _hdelta0, htrade0, _htradeSmall, hlogD⟩ := hscalar q g0 hq hg0 hg01
  change A * u0 ^ 2 / g0 ≤ (s : ℝ) at hsLower
  change (s : ℝ) ≤ (A + 1) * u0 ^ 2 / g0 at hsUpper
  change 21 ≤ s at hs21
  change ell / s = s at hdiv
  change Nat.sqrt ell = s at hsqrt
  change 0 < R0 at hR0
  change (D : ℝ) * delta0 ≤ 1 / 100000 at htrade0
  change log (D : ℝ) ≤ 198 * (A + 1) * (6 + 2 * log (A + 1)) / g0 * u0 ^ 3 at hlogD
  have hlogg : 0 ≤ log (1 / g) := log_nonneg ((one_le_div hg).mpr hg1)
  have hlogg0 : 0 ≤ log (1 / g0) := log_nonneg ((one_le_div hg0).mpr hg01)
  have hlogq : 0 ≤ log (q : ℝ) := log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have hu : 1 ≤ u := by dsimp only [u]; linarith
  have hu0 : 1 ≤ u0 := by dsimp only [u0]; linarith
  have hL : 0 ≤ log (8192 : ℝ) := log_nonneg (by norm_num)
  have hu0eq : u0 = u + log 8192 := by
    have hfrac : 1 / g0 = 8192 * (1 / g) := by dsimp only [g0]; field_simp [hg.ne']
    dsimp only [u0, u]
    rw [hfrac, log_mul (by norm_num : (8192 : ℝ) ≠ 0) (one_div_ne_zero hg.ne')]
    ring
  have hu0le : u0 ≤ (1 + log 8192) * u := by
    rw [hu0eq]
    nlinarith [mul_le_mul_of_nonneg_left hu hL]
  have hlarge : 1 ≤ A * u0 ^ 2 := by
    have hsquare : 1 ≤ u0 ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hsquare (by linarith : 0 ≤ A)
    nlinarith
  have hsInv : 1 / g ≤ (s : ℝ) := by
    calc
      1 / g ≤ 1 / g0 := one_div_le_one_div_of_le hg0 hg0g
      _ ≤ A * u0 ^ 2 / g0 := div_le_div_of_nonneg_right hlarge hg0.le
      _ ≤ (s : ℝ) := hsLower
  have hR : 0 < R := by dsimp only [R, t]; positivity
  have hRbound : R ≤ 2049 * (s : ℝ) := by
    dsimp only [R, t]
    rw [show (1024 : ℝ) / g = 1024 * (1 / g) by ring]
    linarith
  have hsR0 : (s : ℝ) ≤ R0 := by dsimp only [R0, t0]; linarith
  have hRcompare : R ≤ 2049 * R0 :=
    hRbound.trans (mul_le_mul_of_nonneg_left hsR0 (by norm_num))
  have hcoef : (9 * g0 / 10) * 2049 ≤ g / 2 := by dsimp only [g0]; linarith
  have hcross : (9 * g0 / 10) * R ≤ (g / 2) * R0 := by
    have hm := mul_le_mul_of_nonneg_left hRcompare (by positivity : 0 ≤ 9 * g0 / 10)
    have hc := mul_le_mul_of_nonneg_right hcoef hR0.le
    nlinarith
  have hratio : (9 * g0 / 10) / R0 ≤ (g / 2) / R :=
    (div_le_div_iff₀ hR0 hR).mpr hcross
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  have hdeltaLe : delta ≤ delta0 := by
    dsimp only [delta, delta0]
    apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by norm_num)
    apply neg_le_neg
    exact mul_le_mul_of_nonneg_left (sqrt_le_sqrt hratio) (by positivity)
  have htrade : (D : ℝ) * delta ≤ 1 / 100000 :=
    (mul_le_mul_of_nonneg_left hdeltaLe (by positivity : 0 ≤ (D : ℝ))).trans htrade0
  have hsUpper' : (s : ℝ) ≤ 8192 * (A + 1) * (1 + log 8192) ^ 2 / g * u ^ 2 := by
    calc
      (s : ℝ) ≤ (A + 1) * u0 ^ 2 / g0 := hsUpper
      _ ≤ (A + 1) * ((1 + log 8192) * u) ^ 2 / g0 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ u0) hu0le 2)
            (by linarith : 0 ≤ A + 1)) hg0.le
      _ = _ := by dsimp only [g0]; rw [div_div_eq_mul_div]; ring
  have hlogA : 0 ≤ log (A + 1) := log_nonneg (by linarith)
  have hC : 0 ≤ 198 * (A + 1) * (6 + 2 * log (A + 1)) / g0 := by positivity
  refine ⟨hs21, hsInv, hsUpper', hdiv, hsqrt, hR, hdelta, htrade,
    htrade.trans_lt (by norm_num), ?_⟩
  calc
    log (D : ℝ) ≤ 198 * (A + 1) * (6 + 2 * log (A + 1)) / g0 * u0 ^ 3 := hlogD
    _ ≤ 198 * (A + 1) * (6 + 2 * log (A + 1)) / g0 *
        ((1 + log 8192) * u) ^ 3 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ u0) hu0le 3) hC
    _ = _ := by dsimp only [g0]; rw [div_div_eq_mul_div]; ring

end Real

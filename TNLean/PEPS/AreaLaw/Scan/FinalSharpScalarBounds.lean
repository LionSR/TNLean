/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SharpMomentScale
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Scalar ingredients for the final sharp collar comparison

The selected mass has its quantitative `n^(-100)` logarithmic loss; binary
entropy at the prescribed fraction has its full logarithmic smallness; and
the literal rounded band count gives both sides of the per-band scale.
No entropy improvement, physical witness, or replica limit is assumed here.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 839--865 and 883--942, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Filter

namespace TNLean.PEPS.AreaLaw.Scan

/-- The actual selected-mass budget retains its full inverse power after
applying the logarithm. Source: the last error in `scanner:final-errors`. -/
theorem finalSharp_neg_log_mass_le {n : ℕ} (hn : 2 ≤ n) {z : ℝ}
    (hz : 0 < z) (hzupper : z ≤ 1)
    (hmass : 1 - (n : ℝ) ^ (-100 : ℝ) ≤ z) :
    0 ≤ -Real.log z ∧ -Real.log z ≤ 2 * (n : ℝ) ^ (-100 : ℝ) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hsmall : (n : ℝ) ^ (-100 : ℝ) ≤ 1 / 2 := by
    calc
      (n : ℝ) ^ (-100 : ℝ) ≤ (n : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
      _ = (n : ℝ)⁻¹ := Real.rpow_neg_one _
      _ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) hn2
  have hzh : 1 / 2 ≤ z := by linarith
  have hinv : z⁻¹ ≤ 1 + 2 * (n : ℝ) ^ (-100 : ℝ) := by
    rw [← one_div, div_le_iff₀ hz]
    nlinarith [mul_le_mul_of_nonneg_left hzh
      (Real.rpow_nonneg (Nat.cast_nonneg n) (-100 : ℝ))]
  have hlog := Real.one_sub_inv_le_log_of_pos hz
  exact ⟨neg_nonneg.mpr (Real.log_nonpos hz.le hzupper), by linarith⟩

/-- The elementary small-fraction entropy estimate, retaining the logarithm.
It is used at the fixed source fraction `tau = n^(-1/4000)`. -/
theorem finalSharp_binEntropy_le {t : ℝ} (_ht : 0 < t) (htone : t < 1) :
    Real.binEntropy t ≤ t * (1 - Real.log t) := by
  have hq : 0 < 1 - t := sub_pos.mpr htone
  have hlog := mul_le_mul_of_nonneg_right
    (Real.one_sub_inv_le_log_of_pos hq) hq.le
  simp only [sub_mul, one_mul, inv_mul_cancel₀ hq.ne'] at hlog
  simp only [Real.binEntropy, Real.log_inv]
  nlinarith

/-- The source binary-entropy term has exponent `0.74969`, before its
single logarithmic factor, at the final per-band inverse-scale bound. -/
theorem finalSharp_binary_cost_le {n : ℕ} (hn : 2 ≤ n) {a : ℝ}
    (ha : 0 < a) (hinv : 1 / a ≤ (n : ℝ) ^ (37497 / 50000 : ℝ)) :
    (3 + 1 / a) * Real.binEntropy ((n : ℝ) ^ (-(1 / 4000 : ℝ))) ≤
      4 * (n : ℝ) ^ (74969 / 100000 : ℝ) *
        (1 + Real.log (n : ℝ) / 4000) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  have hnlarge : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have ht : 0 < (n : ℝ) ^ (-(1 / 4000 : ℝ)) := by positivity
  have htone : (n : ℝ) ^ (-(1 / 4000 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hnlarge (by norm_num)
  have hentropy := finalSharp_binEntropy_le ht htone
  rw [Real.log_rpow hnpos] at hentropy
  have hpower : 1 ≤ (n : ℝ) ^ (37497 / 50000 : ℝ) :=
    Real.one_le_rpow hn1 (by norm_num)
  have hcoeff : 3 + 1 / a ≤ 4 * (n : ℝ) ^ (37497 / 50000 : ℝ) := by
    linarith
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  calc
    _ ≤ (3 + 1 / a) * ((n : ℝ) ^ (-(1 / 4000 : ℝ)) *
        (1 + Real.log (n : ℝ) / 4000)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      convert hentropy using 1; ring
    _ ≤ (4 * (n : ℝ) ^ (37497 / 50000 : ℝ)) *
        ((n : ℝ) ^ (-(1 / 4000 : ℝ)) *
          (1 + Real.log (n : ℝ) / 4000)) :=
      mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ = _ := by
      rw [← mul_assoc, mul_assoc 4, ← Real.rpow_add hnpos]
      norm_num

/-- The upper power of the literal rounded band count at every `n` from the explicit threshold
`X.scaleFactsThreshold` on, complementing the accepted lower power. No asymptotic replacement
of either floor is made. Source: `scanner:scales`, `08-scanner.tex`, lines 32--41. -/
theorem ScannerExponents.bandCount_le_rpow_of_scaleFactsThreshold_le (X : ScannerExponents)
    {n : ℕ} (hthr : X.scaleFactsThreshold ≤ n) :
    2 ≤ n ∧ (X.K n : ℝ) ≤ (n : ℝ) ^ (1 - X.ell - X.mu) := by
  have hmu : 0 < X.mu := X.kappa_pos.trans X.kappa_lt_mu
  simp only [ScannerExponents.scaleFactsThreshold, max_le_iff] at hthr
  have hn := hthr.1
  have hlarge := Real.le_natCast_rpow_of_natRpowThreshold_le hmu hthr.2.1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm : (n : ℝ) ^ X.mu / 2 ≤ X.m n := half_le_floor hlarge
  have hKL : (X.K n : ℝ) * (8 * (X.m n : ℝ)) ≤ X.L n := by
    exact_mod_cast (Nat.div_mul_le_self (X.L n) (8 * X.m n))
  have hL : (X.L n : ℝ) ≤ (n : ℝ) ^ (1 - X.ell) := Nat.floor_le (by positivity)
  refine ⟨hn, (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hnpos X.mu)).mp ?_⟩
  rw [← Real.rpow_add hnpos,
    show 1 - X.ell - X.mu + X.mu = 1 - X.ell by ring]
  nlinarith [mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (X.K n)),
    mul_nonneg (show (0 : ℝ) ≤ X.K n from Nat.cast_nonneg _)
      (show (0 : ℝ) ≤ X.m n from Nat.cast_nonneg _)]

/-- The upper power of the literal rounded band count, complementing the
accepted lower power. No asymptotic replacement of either floor is made. -/
theorem ScannerExponents.eventually_bandCount_le_rpow (X : ScannerExponents) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧
      (X.K n : ℝ) ≤ (n : ℝ) ^ (1 - X.ell - X.mu) :=
  eventually_atTop.2 ⟨_, fun _ => X.bandCount_le_rpow_of_scaleFactsThreshold_le⟩

/-- The explicit threshold of the final per-band scale bounds: the scale-facts threshold of
the final exponents and `2 ≤ n^(1/4000)` (`08-scanner.tex`, lines 32--41 and 839--865). -/
noncomputable def finalSharpScaleThreshold : ℕ :=
  max finalSharpScannerExponents.scaleFactsThreshold (Real.natRpowThreshold (1 / 4000) 2)

/-- The final scale threshold is at least `2`. -/
theorem two_le_finalSharpScaleThreshold : 2 ≤ finalSharpScaleThreshold :=
  (le_max_left _ _).trans (le_max_left _ _)

/-- The actual rounded source scales have the two required per-band bounds, with the
coefficient `C_a = 32`, and the prescribed final fraction is at most one half, at every `n`
from the explicit threshold `finalSharpScaleThreshold` on. Source: `08-scanner.tex`,
lines 32--41 and 839--865. -/
theorem finalSharp_scale_bounds_of_finalSharpScaleThreshold_le {n : ℕ}
    (hthr : finalSharpScaleThreshold ≤ n) :
    let L := Nat.floor ((n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ)))
    let m := Nat.floor ((n : ℝ) ^ (Exponents.scannerMu : ℝ))
    let K := L / (8 * m)
    let W := (n : ℝ) ^ (Exponents.scannerOmega : ℝ)
    let a := W / (K : ℝ)
    1 ≤ K ∧ 0 < a ∧
      a ≤ 32 * (n : ℝ) ^ (-37497 / 50000 : ℝ) ∧
      1 / a ≤ (n : ℝ) ^ (37497 / 50000 : ℝ) ∧
      0 < (n : ℝ) ^ (-(1 / 4000 : ℝ)) ∧
      (n : ℝ) ^ (-(1 / 4000 : ℝ)) ≤ 1 / 2 := by
  intro L m K W a
  let X := finalSharpScannerExponents
  have hexponent : 1 - X.ell - X.mu = (74999 / 100000 : ℝ) := by
    norm_num [X, finalSharpScannerExponents, Exponents.scannerEll, Exponents.scannerMu]
  have hscale := X.rpow_le_mul_K_of_scaleFactsThreshold_le ((le_max_left _ _).trans hthr)
  have hupper := X.bandCount_le_rpow_of_scaleFactsThreshold_le ((le_max_left _ _).trans hthr)
  have ht : (2 : ℝ) ≤ (n : ℝ) ^ (1 / 4000 : ℝ) :=
    Real.le_natCast_rpow_of_natRpowThreshold_le (by norm_num) ((le_max_right _ _).trans hthr)
  rw [hexponent] at hscale hupper
  obtain ⟨hn2, hK, hlow⟩ := hscale
  have hupp := hupper.2
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < X.K n by omega)
  have hWpos : 0 < W := by dsimp only [W]; positivity
  have ha : 0 < a := div_pos hWpos hKpos
  refine ⟨hK, ha, ?_, ?_, by positivity, ?_⟩
  · apply (div_le_iff₀ hKpos).2
    calc
      W = (n : ℝ) ^ (-37497 / 50000 : ℝ) *
          (n : ℝ) ^ (74999 / 100000 : ℝ) := by
        rw [← Real.rpow_add hnpos]
        norm_num [W, Exponents.scannerOmega]
      _ ≤ (n : ℝ) ^ (-37497 / 50000 : ℝ) * (32 * (K : ℝ)) :=
        mul_le_mul_of_nonneg_left hlow (by positivity)
      _ = _ := by ring
  · change 1 / (W / (K : ℝ)) ≤ _
    rw [one_div_div]
    apply (div_le_iff₀ hWpos).2
    calc
      (K : ℝ) ≤ (n : ℝ) ^ (74999 / 100000 : ℝ) := hupp
      _ = (n : ℝ) ^ (37497 / 50000 : ℝ) * W := by
        dsimp only [W]
        rw [← Real.rpow_add hnpos]
        norm_num [Exponents.scannerOmega]
  · rw [Real.rpow_neg hnpos.le, one_div]
    simpa only [one_div] using inv_anti₀ (by norm_num) ht

/-- The actual rounded source scales have the two required per-band bounds,
and the prescribed final fraction is eventually at most one half. The fixed
coefficient precedes the system size; no physical datum enters it. -/
theorem exists_finalSharp_scale_bounds :
    ∃ Ca : ℝ, 1 ≤ Ca ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      let L := Nat.floor ((n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ)))
      let m := Nat.floor ((n : ℝ) ^ (Exponents.scannerMu : ℝ))
      let K := L / (8 * m)
      let W := (n : ℝ) ^ (Exponents.scannerOmega : ℝ)
      let a := W / (K : ℝ)
      1 ≤ K ∧ 0 < a ∧
        a ≤ Ca * (n : ℝ) ^ (-37497 / 50000 : ℝ) ∧
        1 / a ≤ (n : ℝ) ^ (37497 / 50000 : ℝ) ∧
        0 < (n : ℝ) ^ (-(1 / 4000 : ℝ)) ∧
        (n : ℝ) ^ (-(1 / 4000 : ℝ)) ≤ 1 / 2 :=
  ⟨32, by norm_num, _, two_le_finalSharpScaleThreshold,
    fun _ => finalSharp_scale_bounds_of_finalSharpScaleThreshold_le⟩

/-- The quantitative source trace budget has its actual fixed coefficient.
The first limit is unrelated to this system-size estimate. -/
theorem finalSharp_traceDistance_power {g : ℝ} (hg : 0 < g) {n : ℕ} {t : ℝ}
    (ht : t ≤ Real.sqrt (2 * min ((n : ℝ) ^ (-1000 : ℝ)) (g / 4) / g)) :
    t ≤ Real.sqrt (2 / g) * (n : ℝ) ^ (-500 : ℝ) := by
  have hbound : 2 * min ((n : ℝ) ^ (-1000 : ℝ)) (g / 4) / g ≤
      (2 / g) * (n : ℝ) ^ (-1000 : ℝ) := by
    calc
      _ = (2 / g) * min ((n : ℝ) ^ (-1000 : ℝ)) (g / 4) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
  refine ht.trans ((Real.sqrt_le_sqrt hbound).trans_eq ?_)
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 / g),
    Real.sqrt_eq_rpow ((n : ℝ) ^ (-1000 : ℝ)),
    ← Real.rpow_mul (Nat.cast_nonneg n)]
  norm_num

end TNLean.PEPS.AreaLaw.Scan

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SharpMomentScale
import TNLean.PEPS.AreaLaw.Scan.SubsystemDimensionScale
import TNLean.PEPS.AreaLaw.Scan.BandCountGrowth

/-!
# Fixed-weight transport smallness at the actual logarithmic radius

For any scanner exponents, the literal rounded band count grows with positive
power 1-ell-mu. At total weight four this dominates the fourth-logarithm bound
for the actual transport logarithmic dimension. One threshold therefore gives
at least eight bands and the supplied positive transport-smallness threshold.
Only the generic band-growth theorem from the moment-scale module is used;
no marginal moments or sharp-comparison exponent margin are assumed. The threshold
is given explicitly by `ScannerExponents.fixedWeightTransportThreshold`.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 32--49, 358--359 and 693--755, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

/-- The explicit threshold of the fixed-weight transport smallness: the scale-facts threshold
(band growth `n^{1-ℓ-μ} ≤ 32 K`), `n ≥ 3` (so `log n ≥ 1`), the band-count threshold for
`K ≥ 8`, and the threshold for `128 C_d (log n)^4 ≤ c_t n^{1-ℓ-μ}` with
`C_d = 1 + (2 C_r + 3)^2 log q` (`08-scanner.tex`, lines 49, 358--359 and 693--755). -/
noncomputable def ScannerExponents.fixedWeightTransportThreshold (X : ScannerExponents)
    (q : ℕ) (Cr ct : ℝ) : ℕ :=
  max X.scaleFactsThreshold (max 3 (max (X.bandCountThreshold 8)
    ⌈Real.logPowThreshold (4 * 32 * (1 + (2 * Cr + 3) ^ 2 * Real.log q)) ct
      (1 - X.ell - X.mu) 4⌉₊))

/-- Total weight four satisfies the positive actual transport smallness threshold `ct` at the
source's rounded squared-logarithmic radius, at every `n` from the explicit threshold
`X.fixedWeightTransportThreshold q Cr ct` on.
Source: `08-scanner.tex`, lines 49, 358--359 and 693--755, adc7f124. -/
theorem ScannerExponents.fixedWeightFour_transport_smallness_of_threshold_le
    (X : ScannerExponents) {q : ℕ} (hq : 1 ≤ q)
    {Cr ct : ℝ} (hCr : 0 ≤ Cr) (hct : 0 < ct) {n : ℕ}
    (hthr : X.fixedWeightTransportThreshold q Cr ct ≤ n) :
    8 ≤ X.K n ∧ 0 < X.a 4 n ∧
      X.a 4 n * transportLogDimBound q (roundedLogRadius Cr n) ≤ ct := by
  simp only [fixedWeightTransportThreshold, max_le_iff] at hthr
  obtain ⟨hsf, hn3, hb, hl⟩ := hthr
  have hKn := X.rpow_le_mul_K_of_scaleFactsThreshold_le hsf
  have hK8 := X.le_K_of_bandCountThreshold_le 8 hb
  have hlogn : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    exact Real.exp_one_lt_three.le.trans (by exact_mod_cast hn3)
  have hdim := transportLogDimBound_roundedLogRadius_le hq hCr hlogn
  have hsmall' := Real.mul_log_pow_le_mul_rpow_of_ceil_logPowThreshold_le (by positivity) hct
    (sub_pos.mpr X.mu_lt_one_sub_ell) hl
  generalize hCdef : (32 : ℝ) = C at hKn hsmall'
  generalize (1 + (2 * Cr + 3) ^ 2 * Real.log q) = Cd at hdim hsmall'
  have hCpos : 0 < C := hCdef ▸ by norm_num
  have hKpos : (0 : ℝ) < X.K n := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 8) hK8)
  have ha : 0 < X.a 4 n := div_pos (by norm_num) hKpos
  have hnum : 4 * Cd * Real.log (n : ℝ) ^ 4 ≤ ct * (X.K n : ℝ) := by
    apply (mul_le_mul_iff_of_pos_right hCpos).mp
    calc
      (4 * Cd * Real.log (n : ℝ) ^ 4) * C =
          4 * C * Cd * Real.log (n : ℝ) ^ 4 := by ring
      _ ≤ ct * (n : ℝ) ^ (1 - X.ell - X.mu) := hsmall'
      _ ≤ ct * (C * (X.K n : ℝ)) := mul_le_mul_of_nonneg_left hKn.2.2 hct.le
      _ = (ct * (X.K n : ℝ)) * C := by ring
  refine ⟨hK8, ha, ?_⟩
  calc
    X.a 4 n * transportLogDimBound q (roundedLogRadius Cr n) ≤
        X.a 4 n * (Cd * Real.log (n : ℝ) ^ 4) :=
      mul_le_mul_of_nonneg_left hdim ha.le
    _ = (4 * Cd * Real.log (n : ℝ) ^ 4) / (X.K n : ℝ) := by
      dsimp only [ScannerExponents.a]
      ring
    _ ≤ ct := (div_le_iff₀ hKpos).2 hnum

/-- Total weight four satisfies every fixed positive actual transport
smallness threshold at the source's rounded squared-logarithmic radius.
The physical dimension, radius coefficient, scanner exponents and transport
threshold are fixed before the size. No sharp-margin condition is used.
Source: `08-scanner.tex`, lines 49, 358--359 and 693--755, adc7f124. -/
theorem ScannerExponents.exists_fixedWeightFour_transport_smallness
    (X : ScannerExponents) {q : ℕ} (hq : 1 ≤ q)
    {Cr ct : ℝ} (hCr : 0 ≤ Cr) (hct : 0 < ct) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      8 ≤ X.K n ∧ 0 < X.a 4 n ∧
        X.a 4 n * transportLogDimBound q (roundedLogRadius Cr n) ≤ ct :=
  ⟨_, by unfold fixedWeightTransportThreshold; omega,
    fun _ => X.fixedWeightFour_transport_smallness_of_threshold_le hq hCr hct⟩

end TNLean.PEPS.AreaLaw.Scan

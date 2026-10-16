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
no marginal moments or sharp-comparison exponent margin are assumed.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 32--49, 358--359 and 693--755, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Filter Asymptotics

namespace TNLean.PEPS.AreaLaw.Scan

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
        X.a 4 n * transportLogDimBound q (roundedLogRadius Cr n) ≤ ct := by
  obtain ⟨C, hC, hK⟩ := X.exists_eventually_rpow_le_mul_K
  obtain ⟨Cd, hCd, hdimension⟩ := exists_transportLogDimBound_log_four hq hCr
  have hα : 0 < 1 - X.ell - X.mu := sub_pos.mpr X.mu_lt_one_sub_ell
  have hlog : (fun n : ℕ => 4 * C * Cd * Real.log (n : ℝ) ^ 4) =o[atTop]
      fun n => (n : ℝ) ^ (1 - X.ell - X.mu) := by
    simpa only [Real.rpow_ofNat] using
      ((isLittleO_log_rpow_rpow_atTop 4 hα).natCast_atTop.const_mul_left (4 * C * Cd))
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hK.and (hdimension.and ((hlog.bound hct).and (X.eventually_le_K 8))))
  refine ⟨max N 2, le_max_right _ _, ?_⟩
  intro n hn
  obtain ⟨hKn, hdim, hsmall, hK8⟩ := hN n ((le_max_left N 2).trans hn)
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hKpos : (0 : ℝ) < X.K n := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 8) hK8)
  have ha : 0 < X.a 4 n := div_pos (by norm_num) hKpos
  have hsmall' : 4 * C * Cd * Real.log (n : ℝ) ^ 4 ≤
      ct * (n : ℝ) ^ (1 - X.ell - X.mu) := by
    simpa only [Real.norm_of_nonneg (by positivity :
        0 ≤ 4 * C * Cd * Real.log (n : ℝ) ^ 4),
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)] using hsmall
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

end TNLean.PEPS.AreaLaw.Scan

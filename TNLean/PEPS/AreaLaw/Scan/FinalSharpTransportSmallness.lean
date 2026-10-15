/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.FinalSharpErrorPower
import TNLean.PEPS.AreaLaw.Scan.SubsystemDimensionScale

/-!
# Final per-band weight meets the actual transport smallness condition

The physical logarithmic-dimension cap has its accepted fourth-logarithm
bound. The literal rounded final weight decays with exponent `-0.74994`,
so their product is eventually below every fixed positive threshold.
The threshold precedes the physical instance and all its scanner data.

Source: OpenAI area-law manuscript, `08-scanner.tex`, lines 49, 358--359,
and 839--865, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Filter

namespace TNLean.PEPS.AreaLaw.Scan

/-- The final actual per-band weight satisfies the supplied positive
transport threshold, with the literal squared-logarithmic radius and both
floor operations retained. No transport-smallness hypothesis is assumed. -/
theorem exists_finalSharp_transport_smallness
    {q : ℕ} (hq : 1 ≤ q) {Cr ct : ℝ} (hCr : 0 ≤ Cr) (hct : 0 < ct) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      let L := Nat.floor ((n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ)))
      let m := Nat.floor ((n : ℝ) ^ (Exponents.scannerMu : ℝ))
      let K := L / (8 * m)
      let W := (n : ℝ) ^ (Exponents.scannerOmega : ℝ)
      let a := W / (K : ℝ)
      1 ≤ K ∧ 0 < a ∧ a * transportLogDimBound q (roundedLogRadius Cr n) ≤ ct := by
  obtain ⟨Ca, hCa, Ns, hNs, hscale⟩ := exists_finalSharp_scale_bounds
  obtain ⟨Cd, hCd, hdimension⟩ := exists_transportLogDimBound_log_four hq hCr
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (Ca * Cd / ct) * (n : ℝ) ^ (-37497 / 50000 : ℝ) *
        Real.log (n : ℝ) ^ 4 ≤ 1 := by
    simpa only [Real.rpow_ofNat, Real.rpow_zero] using
      eventually_finalSharp_log_cost_le (Ca * Cd / ct) 4
        (-37497 / 50000) 0 (by positivity) (by norm_num)
  obtain ⟨Nt, hNt⟩ := eventually_atTop.mp (hdimension.and hsmall)
  refine ⟨max Ns Nt, hNs.trans (le_max_left _ _), ?_⟩
  intro n hn L m K W a
  obtain ⟨hK, ha, haUpper, _, _, _⟩ := hscale n ((le_max_left Ns Nt).trans hn)
  obtain ⟨hdim, hsmalln⟩ := hNt n ((le_max_right Ns Nt).trans hn)
  refine ⟨hK, ha, ?_⟩
  calc
    a * transportLogDimBound q (roundedLogRadius Cr n) ≤
        a * (Cd * Real.log (n : ℝ) ^ 4) :=
      mul_le_mul_of_nonneg_left hdim ha.le
    _ ≤ (Ca * (n : ℝ) ^ (-37497 / 50000 : ℝ)) *
        (Cd * Real.log (n : ℝ) ^ 4) :=
      mul_le_mul_of_nonneg_right haUpper (mul_nonneg hCd.le (by positivity))
    _ = ct * ((Ca * Cd / ct) * (n : ℝ) ^ (-37497 / 50000 : ℝ) *
        Real.log (n : ℝ) ^ 4) := by field_simp [hct.ne']
    _ ≤ ct * 1 := mul_le_mul_of_nonneg_left hsmalln hct.le
    _ = ct := mul_one _

end TNLean.PEPS.AreaLaw.Scan

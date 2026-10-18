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
The threshold precedes the physical instance and all its scanner data; it is
given explicitly by `finalSharpTransportThreshold`.

Source: OpenAI area-law manuscript, `08-scanner.tex`, lines 49, 358--359,
and 839--865, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/


namespace TNLean.PEPS.AreaLaw.Scan

/-- The explicit threshold of the final transport smallness: the final scale threshold and
the threshold for `(32 C_d / c_t) n^(-37497/50000) (log n)^4 ≤ 1`, where
`C_d = 1 + (2 C_r + 3)^2 log q` is the transport cap coefficient (`08-scanner.tex`, lines 49,
358--359 and 839--865). It also forces `log n ≥ 1`. -/
noncomputable def finalSharpTransportThreshold (q : ℕ) (Cr ct : ℝ) : ℕ :=
  max finalSharpScaleThreshold
    ⌈Real.logRpowThreshold (32 * (1 + (2 * Cr + 3) ^ 2 * Real.log q) / ct) 1
      (-37497 / 50000) 0 4⌉₊

/-- The final transport threshold is at least `2`. -/
theorem two_le_finalSharpTransportThreshold (q : ℕ) (Cr ct : ℝ) :
    2 ≤ finalSharpTransportThreshold q Cr ct :=
  two_le_finalSharpScaleThreshold.trans (le_max_left _ _)

/-- The final actual per-band weight satisfies the supplied positive transport threshold at
every `n` from the explicit threshold `finalSharpTransportThreshold q Cr ct` on, with the
literal squared-logarithmic radius and both floor operations retained. Source:
`08-scanner.tex`, lines 49, 358--359 and 839--865. -/
theorem finalSharp_transport_smallness_of_threshold_le
    {q : ℕ} (hq : 1 ≤ q) {Cr ct : ℝ} (hCr : 0 ≤ Cr) (hct : 0 < ct) {n : ℕ}
    (hthr : finalSharpTransportThreshold q Cr ct ≤ n) :
    let L := Nat.floor ((n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ)))
    let m := Nat.floor ((n : ℝ) ^ (Exponents.scannerMu : ℝ))
    let K := L / (8 * m)
    let W := (n : ℝ) ^ (Exponents.scannerOmega : ℝ)
    let a := W / (K : ℝ)
    1 ≤ K ∧ 0 < a ∧ a * transportLogDimBound q (roundedLogRadius Cr n) ≤ ct := by
  intro L m K W a
  let Cd := 1 + (2 * Cr + 3) ^ 2 * Real.log q
  have hCd : 0 < Cd := by
    have : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
    positivity
  obtain ⟨hK, ha, haUpper, _, _, _⟩ :=
    finalSharp_scale_bounds_of_finalSharpScaleThreshold_le ((le_max_left _ _).trans hthr)
  have hdim := transportLogDimBound_roundedLogRadius_le hq hCr
    (Real.one_le_log_of_ceil_logRpowThreshold_le ((le_max_right _ _).trans hthr))
  have hsmalln : (32 * Cd / ct) * (n : ℝ) ^ (-37497 / 50000 : ℝ) *
      Real.log (n : ℝ) ^ 4 ≤ 1 := by
    simpa only [Real.rpow_ofNat, Real.rpow_zero, mul_one] using
      Real.mul_rpow_mul_log_rpow_le_mul_rpow_of_ceil_logRpowThreshold_le (by positivity)
        one_pos (by norm_num) ((le_max_right _ _).trans hthr)
  refine ⟨hK, ha, ?_⟩
  calc
    a * transportLogDimBound q (roundedLogRadius Cr n) ≤
        a * (Cd * Real.log (n : ℝ) ^ 4) :=
      mul_le_mul_of_nonneg_left hdim ha.le
    _ ≤ (32 * (n : ℝ) ^ (-37497 / 50000 : ℝ)) *
        (Cd * Real.log (n : ℝ) ^ 4) :=
      mul_le_mul_of_nonneg_right haUpper (mul_nonneg hCd.le (by positivity))
    _ = ct * ((32 * Cd / ct) * (n : ℝ) ^ (-37497 / 50000 : ℝ) *
        Real.log (n : ℝ) ^ 4) := by field_simp [hct.ne']
    _ ≤ ct * 1 := mul_le_mul_of_nonneg_left hsmalln hct.le
    _ = ct := mul_one _

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
      1 ≤ K ∧ 0 < a ∧ a * transportLogDimBound q (roundedLogRadius Cr n) ≤ ct :=
  ⟨_, two_le_finalSharpTransportThreshold q Cr ct,
    fun _ => finalSharp_transport_smallness_of_threshold_le hq hCr hct⟩

end TNLean.PEPS.AreaLaw.Scan

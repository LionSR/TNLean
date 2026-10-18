/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.StatusScaleSeparation
import TNLean.PEPS.AreaLaw.Scan.BandCountGrowth

/-!
# Admissibility of the generic rounded scanner scales

The original literal rounded radius, window, separation and band count obey
the displayed numerical scanner inequalities for every fixed exponent tuple.
The doubled radius supports source truncation, and at least eight bands
support the fixed-total-weight rough lower comparison. The threshold precedes
all finite domains, cuts, Hamiltonians, templates and entropy data; it is given
explicitly by `ScannerExponents.roundedAdmissibilityThreshold`.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 32--58 and 693--755, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

/-- The explicit threshold of the rounded scanner inequalities: the status scale separation
threshold, the rounded-radius threshold for `2 ⌈Cr log² n⌉ ≤ n^κ`, and the band-count
threshold for `K ≥ 8` (`08-scanner.tex`, lines 32--58 and 693--755). -/
noncomputable def ScannerExponents.roundedAdmissibilityThreshold (X : ScannerExponents)
    (Cr : ℝ) : ℕ :=
  max (statusScaleSeparationThreshold Cr X.kappa X.mu)
    (max (roundedLogRadiusThreshold Cr X.kappa 2 1) (X.bandCountThreshold 8))

/-- The actual rounded numerical scanner inequalities, with at least eight bands, hold at
every `n` from the explicit threshold `X.roundedAdmissibilityThreshold Cr` on.
Source: `08-scanner.tex`, lines 32--58 and 693--755, adc7f124. -/
theorem ScannerExponents.rounded_admissibility_of_threshold_le
    (X : ScannerExponents) {Cr : ℝ} (hCr : 0 ≤ Cr) {n : ℕ}
    (hthr : X.roundedAdmissibilityThreshold Cr ≤ n) :
    2 * roundedLogRadius Cr n ≤ X.D n ∧ 1 ≤ X.D n ∧
      4 * X.D n ≤ X.m n ∧ 8 ≤ X.K n ∧ 8 * X.K n * X.m n ≤ X.L n := by
  simp only [roundedAdmissibilityThreshold, max_le_iff] at hthr
  obtain ⟨hs, hr, hb⟩ := hthr
  have hscale := status_scale_separation_of_threshold_le
    (ell := X.ell) hCr X.kappa_pos X.kappa_lt_mu hs
  have hradius := const_mul_roundedLogRadius_pow_le_rpow_of_threshold_le hCr X.kappa_pos 2 1 hr
  rw [pow_one] at hradius
  dsimp only at hscale
  refine ⟨?_, hscale.2.2.1, hscale.2.2.2.1, X.le_K_of_bandCountThreshold_le 8 hb,
    hscale.2.2.2.2⟩
  exact_mod_cast hradius.trans (Nat.le_ceil ((n : ℝ) ^ X.kappa))

/-- Every fixed scanner exponent tuple and nonnegative radius coefficient
give one threshold for the actual rounded numerical scanner inequalities.
The same threshold supplies at least eight bands; no final-stage exponent
choices or sharp-margin assumptions are used.
Source: `08-scanner.tex`, lines 32--58 and 693--755, adc7f124. -/
theorem ScannerExponents.exists_rounded_admissibility
    (X : ScannerExponents) {Cr : ℝ} (hCr : 0 ≤ Cr) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      2 * roundedLogRadius Cr n ≤ X.D n ∧ 1 ≤ X.D n ∧
        4 * X.D n ≤ X.m n ∧ 8 ≤ X.K n ∧ 8 * X.K n * X.m n ≤ X.L n :=
  ⟨_, by unfold roundedAdmissibilityThreshold roundedLogRadiusThreshold; omega,
    fun _ => X.rounded_admissibility_of_threshold_le hCr⟩

end TNLean.PEPS.AreaLaw.Scan

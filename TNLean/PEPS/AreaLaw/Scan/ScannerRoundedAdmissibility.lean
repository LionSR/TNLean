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
all finite domains, cuts, Hamiltonians, templates and entropy data.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 32--58 and 693--755, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Filter

namespace TNLean.PEPS.AreaLaw.Scan

/-- Every fixed scanner exponent tuple and nonnegative radius coefficient
give one threshold for the actual rounded numerical scanner inequalities.
The same threshold supplies at least eight bands; no final-stage exponent
choices or sharp-margin assumptions are used.
Source: `08-scanner.tex`, lines 32--58 and 693--755, adc7f124. -/
theorem ScannerExponents.exists_rounded_admissibility
    (X : ScannerExponents) {Cr : ℝ} (hCr : 0 ≤ Cr) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      2 * roundedLogRadius Cr n ≤ X.D n ∧ 1 ≤ X.D n ∧
        4 * X.D n ≤ X.m n ∧ 8 ≤ X.K n ∧ 8 * X.K n * X.m n ≤ X.L n := by
  have hscales := eventually_status_scale_separation
    (ell := X.ell) hCr X.kappa_pos X.kappa_lt_mu
  have hradius := eventually_const_mul_roundedLogRadius_le_rpow hCr X.kappa_pos 2
  have hbands := X.eventually_le_K 8
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hscales.and (hradius.and hbands))
  refine ⟨max N 2, le_max_right _ _, ?_⟩
  intro n hn
  obtain ⟨hscale, hradius, hband⟩ := hN n ((le_max_left N 2).trans hn)
  dsimp only at hscale
  refine ⟨?_, hscale.2.2.1, hscale.2.2.2.1, hband, hscale.2.2.2.2⟩
  exact_mod_cast hradius.trans (Nat.le_ceil ((n : ℝ) ^ X.kappa))

end TNLean.PEPS.AreaLaw.Scan

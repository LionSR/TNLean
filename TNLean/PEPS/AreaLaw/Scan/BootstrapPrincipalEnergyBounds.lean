/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.PEPS.AreaLaw.Scan.BootstrapParameters
import TNLean.PEPS.AreaLaw.Scan.Budgets
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The numerical energy expression at the fixed bootstrap scales

Fix the initial exponent and all scalar and logarithmic coefficients before
the system size. The total metric weight is four. The threshold is uniform
in the current entropy exponent below the initial exponent. The collar and
window retain their floors, the number of bands retains its natural-number
division, and the separation retains its ceiling.

The principal term of the scanner energy estimate is bounded at the fixed
scales below. The statement excludes the fixed term \(C n^{-1000}\) and the
remainder that tends to zero with the replica count. No physical energy
estimate is assumed, and no scan or entropy improvement is constructed.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, `scanner:density-output`, lines 379–384;
`scanner:energy-output`, lines 371–377; `scanner:bootstrap-parameters`,
lines 693–703; and `scanner:bootstrap-energy`, lines 731–755, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Filter Asymptotics
open scoped Topology

namespace TNLean.PEPS.AreaLaw.Scan

/-- With total metric weight four, the rounded principal energy expression
is eventually below the bootstrap energy scale. Every coefficient is fixed
before the threshold, which precedes every current exponent `e ≤ e₀`.
The unit coefficient in the conclusion is obtained by increasing the threshold.
This is a numerical auxiliary to `08-scanner.tex`, lines 731–755;
no defect energy or entropy estimate is assumed. The proof remains unfinished. -/
theorem exists_bootstrap_principal_energy_bound
    {e₀ : ℝ} (he₀ : 0 < e₀) (he₀₁ : e₀ < 1)
    (C Cδ Cl Clδ : ℝ) (hC : 0 ≤ C) (hCδ : 0 ≤ Cδ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ e : ℝ, e ≤ e₀ →
        let ℓ := BootstrapParameters.ell e₀
        let μ := BootstrapParameters.mu e₀
        let ν := BootstrapParameters.nu e₀
        let κ := BootstrapParameters.kappa e₀
        let L := Nat.floor ((n : ℝ) ^ (1 - ℓ))
        let m := Nat.floor ((n : ℝ) ^ μ)
        let K := L / (8 * m)
        let D := Nat.ceil ((n : ℝ) ^ κ)
        let a : ℝ := 4 / (K : ℝ)
        let δ := Cδ * ((n : ℝ) ^ (-ν))⁻¹ *
          ((n : ℝ) ^ (e - μ) + a ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ^ Clδ)
        C * (n : ℝ) ^ ℓ * (D : ℝ) ^ 2 * (4 : ℝ) ^ 2 *
            Real.log (n : ℝ) ^ Cl *
            (δ ^ (1 / 8 : ℝ) + (n : ℝ) ^ (-ν) + (n : ℝ) ^ (-100 : ℝ)) ≤
          (n : ℝ) ^ (-ν / 2) := by
  have hlog := (isLittleO_log_rpow_rpow_atTop Clδ
    (show 0 < BootstrapParameters.nu e₀ by
      dsimp only [BootstrapParameters.nu, BootstrapParameters.g0]
      linarith)).natCast_atTop
  done

end TNLean.PEPS.AreaLaw.Scan

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.Exponents
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Fixed parameters for improvement of the safe-box exponent

For an initial exponent `0 < e₀ < 1`, the parameters used to improve the safe-box
entropy estimate are fixed throughout the iteration. The two density-error
exponents lie strictly below `-0.24 g₀`; addition of the energy-prefactor exponent
leaves both energy-error exponents strictly below `-ν / 2`. The remaining comparison
terms have exponents below the improved entropy exponent.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24,
  2026, proof of Proposition `prop:small-box`, `scanner:bootstrap-parameters` and
  `scanner:bootstrap-energy`, `08-scanner.tex`, lines 693–787.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

The proofs are independent formalizations of the manuscript's scalar calculations;
no upstream Lean proof text is reused.
-/

noncomputable section

/-
Source: September 24, 2026, OpenAI, A two-dimensional area law from a global spectral gap.
Manuscript section: 08-scanner.tex.
Labels: prop:small-box; scanner:bootstrap-parameters; scanner:bootstrap-energy.
Independently formalized; no upstream Lean proof text reused.
Provenance-ID: 8756-tnlean.peps.arealaw.scan.bootstrapparameters.g0
Downstream declaration: TNLean.PEPS.AreaLaw.Scan.BootstrapParameters.g0
Provenance-ID: 8756-tnlean.peps.arealaw.scan.bootstrapparameters.mu
Downstream declaration: TNLean.PEPS.AreaLaw.Scan.BootstrapParameters.mu
Provenance-ID: 8756-tnlean.peps.arealaw.scan.bootstrapparameters.nu
Downstream declaration: TNLean.PEPS.AreaLaw.Scan.BootstrapParameters.nu
Provenance-ID: 8756-tnlean.peps.arealaw.scan.bootstrapparameters.ell
Downstream declaration: TNLean.PEPS.AreaLaw.Scan.BootstrapParameters.ell
Provenance-ID: 8756-tnlean.peps.arealaw.scan.bootstrapparameters.kappa
Downstream declaration: TNLean.PEPS.AreaLaw.Scan.BootstrapParameters.kappa
Provenance-ID: 8756-tnlean.peps.arealaw.scan.bootstrapparameters.parameter_bounds
Downstream declaration: TNLean.PEPS.AreaLaw.Scan.BootstrapParameters.parameter_bounds
Provenance-ID: 8756-tnlean.peps.arealaw.scan.bootstrapparameters.density_exponents
Downstream declaration: TNLean.PEPS.AreaLaw.Scan.BootstrapParameters.density_exponents
Provenance-ID: 8756-tnlean.peps.arealaw.scan.bootstrapparameters.energy_exponents
Downstream declaration: TNLean.PEPS.AreaLaw.Scan.BootstrapParameters.energy_exponents
Provenance-ID: 8756-tnlean.peps.arealaw.scan.bootstrapparameters.comparison_exponents
Downstream declaration: TNLean.PEPS.AreaLaw.Scan.BootstrapParameters.comparison_exponents
-/

namespace TNLean.PEPS.AreaLaw.Scan.BootstrapParameters

/-- The fixed gap `g₀ = (1 - e₀) / 2` from `scanner:bootstrap-parameters`. -/
def g0 (e0 : ℝ) : ℝ := (1 - e0) / 2

/-- The fixed scanner exponent `μ = 1 - g₀` from `scanner:bootstrap-parameters`. -/
def mu (e0 : ℝ) : ℝ := 1 - g0 e0

/-- The fixed error exponent `ν = g₀ / 1000` from `scanner:bootstrap-parameters`. -/
def nu (e0 : ℝ) : ℝ := g0 e0 / 1000

/-- The fixed improvement fraction `ℓ = ν / 100` from
`scanner:bootstrap-parameters`. -/
def ell (e0 : ℝ) : ℝ := nu e0 / 100

/-- The fixed separation exponent `κ = min(ℓ, e_* / 4)` from
`scanner:bootstrap-parameters`, using the manuscript's final box exponent. -/
def kappa (e0 : ℝ) : ℝ := min (ell e0) ((Exponents.boxError : ℝ) / 4)

/-- The fixed gap and improvement fraction lie in their required intervals, and the
separation exponent is positive. Source: `scanner:bootstrap-parameters`. -/
theorem parameter_bounds {e0 : ℝ} (h0 : 0 < e0) (h1 : e0 < 1) :
    0 < g0 e0 ∧ g0 e0 < 1 / 2 ∧ 0 < ell e0 ∧ ell e0 < 1 ∧ 0 < kappa e0 := by
  norm_num [g0, ell, nu, kappa, Exponents.boxError, lt_min_iff]
  exact ⟨h1, by linarith, h1, by linarith, h1⟩

/-- The two density-error exponents have a strict margin below `-0.24 g₀`, uniformly
for every current entropy exponent `e ≤ e₀`.
Source: proof of `prop:small-box`, `08-scanner.tex`, lines 737–744. -/
theorem density_exponents {e0 e : ℝ} (h1 : e0 < 1) (he : e ≤ e0) :
    e0 - mu e0 + nu e0 = -(999 / 1000 : ℝ) * g0 e0 ∧
    -(g0 e0 - ell e0) / 4 + nu e0 = -(99599 / 400000 : ℝ) * g0 e0 ∧
    e - mu e0 + nu e0 < -(6 / 25 : ℝ) * g0 e0 ∧
    -(g0 e0 - ell e0) / 4 + nu e0 < -(6 / 25 : ℝ) * g0 e0 := by
  dsimp [mu, nu, ell, g0]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The energy prefactor has exponent at most `0.00003 g₀`. Both its products with
the error `n ^ (-ν)` and the eighth root of the density error have exponents
strictly below `-ν / 2`.
Source: proof of `scanner:bootstrap-energy`, `08-scanner.tex`, lines 744–752. -/
theorem energy_exponents {e0 : ℝ} (h1 : e0 < 1) :
    ell e0 + 2 * kappa e0 ≤ (3 / 100000 : ℝ) * g0 e0 ∧
    ell e0 + 2 * kappa e0 - nu e0 < -nu e0 / 2 ∧
    ell e0 + 2 * kappa e0 - (3 / 100 : ℝ) * g0 e0 < -nu e0 / 2 := by
  have hk : kappa e0 ≤ ell e0 := min_le_left _ _
  dsimp [ell, nu, g0] at hk ⊢
  exact ⟨by linarith, by linarith, by linarith⟩

/-- The separation term is dominated by the improved entropy exponent, and the
entropy-continuity term has exponent strictly below one.
Source: proof of `prop:small-box`, `08-scanner.tex`, lines 772–779. -/
theorem comparison_exponents {e0 e : ℝ} (h0 : 0 < e0)
    (he : (Exponents.boxError : ℝ) < e) :
    kappa e0 < (1 - ell e0) * e ∧ g0 e0 - ell e0 - nu e0 / 4 < 1 := by
  constructor
  · have hk : kappa e0 ≤ (Exponents.boxError : ℝ) / 4 := min_le_right _ _
    norm_num [ell, nu, g0, Exponents.boxError] at he hk ⊢
    nlinarith [mul_pos h0 (by linarith : 0 < e)]
  · dsimp [g0, ell, nu]
    linarith

end TNLean.PEPS.AreaLaw.Scan.BootstrapParameters

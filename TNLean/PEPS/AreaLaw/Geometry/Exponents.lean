/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Tactic.NormNum

/-!
# Exact exponents for the final area-law argument

All numerical exponents are rational numbers. Their real values are obtained
by coercion. The parameter-dependent exponents of the initial entropy bound
are not identified with these final choices.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `scanner:final-parameters`,
  `eq:amplification-exponents`, `geometry:exponents`, `geometry:exponent-gaps`.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/08-scanner.tex
Labels: scanner:final-parameters.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/09-amplification.tex
Labels: eq:amplification-exponents.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex
Labels: geometry:exponent-gaps.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex
Labels: geometry:exponents.
Provenance-ID: 8738-tnlean.peps.arealaw.exponents.boxerror
Downstream declaration: TNLean.PEPS.AreaLaw.Exponents.boxError
Provenance-ID: 8738-tnlean.peps.arealaw.exponents.scannermu
Downstream declaration: TNLean.PEPS.AreaLaw.Exponents.scannerMu
Provenance-ID: 8738-tnlean.peps.arealaw.exponents.scannernu
Downstream declaration: TNLean.PEPS.AreaLaw.Exponents.scannerNu
Provenance-ID: 8738-tnlean.peps.arealaw.exponents.scannerell
Downstream declaration: TNLean.PEPS.AreaLaw.Exponents.scannerEll
Provenance-ID: 8738-tnlean.peps.arealaw.exponents.scanneromega
Downstream declaration: TNLean.PEPS.AreaLaw.Exponents.scannerOmega
Provenance-ID: 8738-tnlean.peps.arealaw.exponents.scannerkappa
Downstream declaration: TNLean.PEPS.AreaLaw.Exponents.scannerKappa
Provenance-ID: 8738-tnlean.peps.arealaw.exponents.amplificationepsilon
Downstream declaration: TNLean.PEPS.AreaLaw.Exponents.amplificationEpsilon
Provenance-ID: 8738-tnlean.peps.arealaw.exponents.beta
Downstream declaration: TNLean.PEPS.AreaLaw.Exponents.beta
Provenance-ID: 8738-tnlean.peps.arealaw.exponents.amplificationpower
Downstream declaration: TNLean.PEPS.AreaLaw.Exponents.amplificationPower
Provenance-ID: 8738-tnlean.peps.arealaw.exponents.alpha
Downstream declaration: TNLean.PEPS.AreaLaw.Exponents.alpha
Provenance-ID: 8738-tnlean.peps.arealaw.exponents.geometrydelta
Downstream declaration: TNLean.PEPS.AreaLaw.Exponents.geometryDelta
Provenance-ID: 8738-tnlean.peps.arealaw.exponents.zeta
Downstream declaration: TNLean.PEPS.AreaLaw.Exponents.zeta
Provenance-ID: 8738-tnlean.peps.arealaw.exponents.rho
Downstream declaration: TNLean.PEPS.AreaLaw.Exponents.rho
Provenance-ID: 8738-tnlean.peps.arealaw.exponents.geometryell
Downstream declaration: TNLean.PEPS.AreaLaw.Exponents.geometryEll
Provenance-ID: 8738-tnlean.peps.arealaw.exponents.alpha_gt
Downstream declaration: TNLean.PEPS.AreaLaw.Exponents.alpha_gt
Provenance-ID: 8738-tnlean.peps.arealaw.exponents.geometry_gaps
Downstream declaration: TNLean.PEPS.AreaLaw.Exponents.geometry_gaps
-/

namespace TNLean.PEPS.AreaLaw.Exponents

/-- Final safe-box error exponent `e_* = 2·10⁻⁶`.
Source: Section 9, before `scanner:final-parameters`. -/
def boxError : ℚ := 2 / 1000000

/-- Scanner exponent `μ`. Source: `scanner:final-parameters`. -/
def scannerMu : ℚ := 1 / 4

/-- Scanner exponent `ν`. Source: `scanner:final-parameters`. -/
def scannerNu : ℚ := 1 / 1000

/-- Scanner exponent `ℓ`. Source: `scanner:final-parameters`. -/
def scannerEll : ℚ := 1 / 100000

/-- Scanner exponent `ω`. Source: `scanner:final-parameters`. -/
def scannerOmega : ℚ := 1 / 20000

/-- Scanner exponent `κ`. Source: `scanner:final-parameters`. -/
def scannerKappa : ℚ := 1 / 1000000

/-- Amplification exponent `ε`. Source: `eq:amplification-exponents`. -/
def amplificationEpsilon : ℚ := 1 / 100000

/-- Amplification exponent `β`. Source: `eq:amplification-exponents`. -/
def beta : ℚ := 1 - boxError

/-- One fixed integer meeting the source's requirement on `p`.
Source: `eq:amplification-exponents`; this is a permissible explicit choice. -/
def amplificationPower : ℕ := 1000000

/-- Stretched-exponential exponent `α = p/(p+1)` for the fixed choice of `p`.
Source: `eq:amplification-exponents`. -/
def alpha : ℚ := amplificationPower / (amplificationPower + 1 : ℚ)

/-- Geometric exponent `δ₀`. Source: `geometry:exponents`. -/
def geometryDelta : ℚ := 2 / 10000000

/-- Geometric exponent `ζ`. Source: `geometry:exponents`. -/
def zeta : ℚ := 1 - geometryDelta / 2

/-- Geometric exponent `ρ₀`. Source: `geometry:exponents`. -/
def rho : ℚ := (1 + beta) / 2

/-- Geometric exponent `ℓ`. Source: `geometry:exponents`. -/
def geometryEll : ℚ := 1 / 100000

/-- The chosen integer satisfies the source's strict amplification requirement. -/
theorem alpha_gt : 1 - (1 / 1000000 : ℚ) < alpha := by
  norm_num [alpha, amplificationPower]

/-- The geometric exponent gaps hold as exact rational inequalities.
Source: `geometry:exponent-gaps`. -/
theorem geometry_gaps :
    (1 + 2 * geometryDelta) * beta < zeta ∧ zeta < 1 ∧
    (1 + 2 * geometryDelta) * (1 - geometryEll) < 1 ∧
    1 - geometryEll < beta ∧ beta < rho ∧ rho < 1 := by
  norm_num [geometryDelta, beta, boxError, zeta, geometryEll, rho]

end TNLean.PEPS.AreaLaw.Exponents

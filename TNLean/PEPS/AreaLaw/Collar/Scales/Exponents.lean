/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Tactic.NormNum
import QICLean.ManyBody.Sites.Template.Defs
import QICLean.ManyBody.Sites.Dyadic.CellCounting
import QICLean.ManyBody.Sites.Lattice.SupDistance

/-!
# Exact exponents for the final area-law argument

All numerical exponents are rational numbers. Their real values are obtained
by coercion. The parameter-dependent exponents of the initial entropy bound
are not identified with these final choices.

The module also states Proposition 11.2 (`prop:two-families`) as the predicate
`TwoFamilyDecomposition`, with these exponents: every cut has an ordered two-family partition
whose pieces lie in separated templates. It is proved in
`BirthRegions/FinalRegions/TwoFamilyAssembly`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `scanner:final-parameters`,
  `eq:amplification-exponents`, `geometry:exponents`, `geometry:exponent-gaps`.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
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

open scoped BigOperators

namespace TNLean.PEPS.AreaLaw

section TwoFamilyDecomposition

open ManyBody (planeDomainGraph edgeBoundary supDist)

/-- **Proposition 11.2** (`prop:two-families`, `10-geometry.tex` lines 98–140),
for the template constants `D₀, Ctpl` of Definition 9.3. For every lower scale
threshold `n_* ≥ 1` there is a constant `C` such that every cut `A` of a finite
induced domain with `b = |∂_Λ A| > 0` has an ordered partition
`A = D ∪ ⋃ᵢ Xᵢ` into two labelled families of nonempty pieces, with templates
`Tᵢ` of parameters `(nᵢ, sᵢ)` separated from the cut endpoints `Z`, such that
`|D| ≤ C b`, `Xᵢ ⊆ A ∩ Tᵢ`, `⌊nᵢ^(1-ℓ)⌋ ≤ sᵢ`, `nᵢ ≥ n_*`, the clearances
`dist_∞(Tᵢ, Z) > 2 nᵢ^β` and `dist_∞(Tᵢ, ⋃_{j<i, fⱼ=fᵢ} Xⱼ) > 2 nᵢ^β` hold, and
`∑ᵢ nᵢ^(-100) ≤ C b`. The constant is chosen before the domain and the cut. -/
def TwoFamilyDecomposition (D₀ Ctpl : ℝ) : Prop :=
  ∀ nstar : ℕ, 1 ≤ nstar → ∃ C : ℝ,
    ∀ Λ : Finset (ℤ × ℤ), ∀ A : Finset ↥Λ, 0 < (edgeBoundary (planeDomainGraph Λ) A).card →
      ∃ P : ManyBody.OrderedTwoFamilyPartition A, ∃ n s : Fin P.pieceCount → ℕ,
        ∃ T : ∀ i, ManyBody.Template Ctpl (n i) (s i),
          (P.residual.card : ℝ) ≤ C * (edgeBoundary (planeDomainGraph Λ) A).card ∧
          (∀ i, (P.piece i).Nonempty) ∧
          (∀ i, P.piece i ⊆ A.filter fun x ↦ x.val ∈ (T i).points) ∧
          (∀ i, (T i).IsSeparated D₀ (ManyBody.boundaryEndpoints Λ A)) ∧
          (∀ i, ⌊(n i : ℝ) ^ (1 - (Exponents.geometryEll : ℝ))⌋₊ ≤ s i) ∧
          (∀ i, nstar ≤ n i) ∧
          (∀ i, ∀ t ∈ (T i).points, ∀ z ∈ ManyBody.boundaryEndpoints Λ A,
            2 * (n i : ℝ) ^ (Exponents.beta : ℝ) < ((supDist t z : ℤ) : ℝ)) ∧
          (∀ i, ∀ t ∈ (T i).points, ∀ x ∈ P.earlierSameFamily i,
            2 * (n i : ℝ) ^ (Exponents.beta : ℝ) < ((supDist t x.val : ℤ) : ℝ)) ∧
          ∑ i, ((n i : ℝ) ^ 100)⁻¹ ≤ C * (edgeBoundary (planeDomainGraph Λ) A).card

end TwoFamilyDecomposition

end TNLean.PEPS.AreaLaw

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.RegionalEntropy

/-!
# The uniform finite-domain area-law statement

The constant is chosen before the finite domain, interaction family, ground
vector, and cut. Regional entropy is the von Neumann entropy of the partial
trace from `TNLean.Lattice.RegionalEntropy`. The target is a proposition; this
module does not assert that the area law has been proved.

## Main definitions

* `UniformAreaLaw`: the complete arbitrary-domain, finite-range target.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Theorem 1.1 and `eq:area-law`.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw

/-- The uniform area-law target, with its constant chosen before all physical
instances. Source: area-law Theorem 1.1 (`thm:area`, `eq:area-law`).
This proposition is a theorem statement, not a proof of that theorem. -/
def UniformAreaLaw : Prop :=
  ∀ q : ℕ, 1 ≤ q → ∀ R : ℕ, ∀ J Δ : ℝ, 0 < J → 0 < Δ →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ Λ : Finset (ℤ × ℤ), ∀ h : LocalHamiltonian Λ q R J,
        ∀ E₀ : ℝ, ∀ Ω : StateSpace Λ q,
          IsGappedGroundState Λ q h.operator E₀ Ω Δ →
            ∀ A : Finset (Site Λ), regionalEntropy Λ q Ω A ≤ C * (edgeBoundary Λ A).card

end TNLean.PEPS.AreaLaw

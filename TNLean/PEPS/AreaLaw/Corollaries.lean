/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RectangularSpecialization
import TNLean.PEPS.AreaLaw.UniformAreaLaw

/-!
# Rectangular, vertex-boundary and square-grid consequences of the area law

The rectangular conclusion retains arbitrary natural side lengths and
local dimension at least one. The vertex-boundary conclusion applies to
arbitrary finite induced domains and interaction ranges. The square-grid
conclusion uses the existing original-model predicate, with local dimension
at least two. In each case the constant precedes the domain, interaction
family, ground vector and cut.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Corollary 1.2 (`cor:rectangles`),
`00-introduction.tex`, lines 60–85; and *Polynomial PEPS approximation of
gapped square-grid ground states*, Proposition 2.1 (`prop:area-law`),
`01-preliminaries.tex`, lines 39–56. Source revision:
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized; no upstream Lean proof text reused.
-/

namespace TNLean.PEPS.AreaLaw

/-- The uniform entropy bound on arbitrary native rectangles, with the same
constant for the edge and both vertex-boundary forms.
Source: area-law Corollary 1.2 (`cor:rectangles`), lines 69–85. -/
theorem rectangularEntropyAreaLaw : RectangularEntropyAreaLaw := by
  exact UniformAreaLaw.rectangularEntropyAreaLaw uniformAreaLaw

/-- The two vertex-boundary consequences on arbitrary finite induced domains,
with one constant chosen before every physical instance and cut.
Source: area-law Corollary 1.2 (`cor:rectangles`), lines 60–85. -/
theorem vertex_boundary_bounds :
    ∀ q : ℕ, 1 ≤ q → ∀ R : ℕ, ∀ J Δ : ℝ, 0 < J → 0 < Δ →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ Λ : Finset (ℤ × ℤ), ∀ H : LocalHamiltonian Λ q R J,
          ∀ E₀ : ℝ, ∀ Ω : StateSpace Λ q,
            IsGappedGroundState Λ q H.operator E₀ Ω Δ →
              ∀ A : Finset (Site Λ),
                regionalEntropy Λ q Ω A ≤ 4 * C * (innerBoundary Λ A).card ∧
                regionalEntropy Λ q Ω A ≤ 2 * C * (endpointBoundary Λ A).card := by
  exact UniformAreaLaw.vertex_boundary_bounds uniformAreaLaw

/-- The original square-grid entropy area law, with its constant chosen
before the side length, interaction family, ground vector and cut.
Source: polynomial-PEPS Proposition 2.1 (`prop:area-law`), lines 39–56,
derived there from area-law Theorem 1.1 and Corollary 1.2. -/
theorem squareEntropyAreaLaw : Approximation.SquareEntropyAreaLaw := by
  exact UniformAreaLaw.squareEntropyAreaLaw uniformAreaLaw

end TNLean.PEPS.AreaLaw

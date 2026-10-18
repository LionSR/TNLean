/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.BoundaryTheoremFromTwoFamilies
import TNLean.PEPS.AreaLaw.Geometry.TwoFamilyAssembly
import TNLean.PEPS.AreaLaw.RectangularSpecialization
import TNLean.PEPS.AreaLaw.VertexBoundaryCorollaries

/-!
# The two-dimensional area law

Theorem 1.1 of the area-law manuscript: for every finite induced domain of the
square lattice, every admissible local Hamiltonian with a gapped ground state
and every cut, the regional entropy is at most a constant times the number of
cut edges, with the constant chosen before the domain, Hamiltonian, state and
cut. Corollary 1.2 restates the bound for the vertex boundaries and for
rectangles.

## Main results

* `uniformAreaLaw`: Theorem 1.1.
* `uniformAreaLaw_vertex_boundary_bounds`, `rectangularEntropyAreaLaw`:
  Corollary 1.2.
* `squareEntropyAreaLaw`: the square-grid specialization used by the
  polynomial-PEPS manuscript as Proposition 2.1.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Theorem 1.1 (`00-introduction.tex`, lines 39–53) and
  Corollary 1.2 (lines 69–86), with the proof in `10-geometry.tex`,
  lines 803–857. Source revision:
  `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw

/-- Theorem 1.1 of the area-law manuscript, `00-introduction.tex`, lines 39–53:
the uniform boundary law for gapped ground states on finite induced domains of
the square lattice. -/
theorem uniformAreaLaw : UniformAreaLaw :=
  uniformAreaLaw_of_twoFamilies fun R ↦
    ⟨2 * R + 11, 24, by linarith, le_rfl, twoFamilyDecomposition _ _⟩

/-- Corollary 1.2 of the area-law manuscript, `00-introduction.tex`, lines
69–86: the uniform bound in terms of the inner and the endpoint vertex
boundaries. -/
theorem uniformAreaLaw_vertex_boundary_bounds :
    ∀ q : ℕ, 1 ≤ q → ∀ R : ℕ, ∀ J Δ : ℝ, 0 < J → 0 < Δ →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ Λ : Finset (ℤ × ℤ), ∀ H : LocalHamiltonian Λ q R J,
          ∀ E₀ : ℝ, ∀ Ω : StateSpace Λ q,
            IsGappedGroundState Λ q H.operator E₀ Ω Δ →
              ∀ A : Finset (Site Λ),
                regionalEntropy Λ q Ω A ≤ 4 * C * (innerBoundary Λ A).card ∧
                regionalEntropy Λ q Ω A ≤ 2 * C * (endpointBoundary Λ A).card :=
  uniformAreaLaw.vertex_boundary_bounds

/-- Corollary 1.2 of the area-law manuscript for rectangles,
`00-introduction.tex`, lines 69–86. -/
theorem rectangularEntropyAreaLaw : RectangularEntropyAreaLaw :=
  uniformAreaLaw.rectangularEntropyAreaLaw

/-- The square-grid entropy area law, Proposition 2.1 of the polynomial-PEPS
manuscript, `01-preliminaries.tex`, lines 39–58. -/
theorem squareEntropyAreaLaw : Approximation.SquareEntropyAreaLaw :=
  rectangularEntropyAreaLaw.squareEntropyAreaLaw

end TNLean.PEPS.AreaLaw

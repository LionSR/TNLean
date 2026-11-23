/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Sites.Lattice.Square
import QICLean.ManyBody.Hamiltonian.Models
import TNLean.PEPS.Injectivity.Normal.NormalBlocking
import QICLean.ManyBody.Sites.ProductOperatorTrace
import QICLean.Circuit.Geometry
import Mathlib.Data.Finset.NoncommProd
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import QICLean.ManyBody.Hamiltonian.GroundSpace
import QICLean.Algebra.Kronecker.FiniteKroneckerProduct
import QICLean.ManyBody.Sites.ProductVector

/-!
# The polynomial-bond PEPS approximation statement

The input is an open square-grid Hamiltonian. Only its total sum is required
to be Hermitian. The approximating tensor is a native graph PEPS on the same
edges, with positive edge dimensions and nonzero contraction. Error concerns
the normalized global vector, with a freely chosen phase.

## Main definitions

* `IsSquareGroundState`: the unit gapped ground vectors of the model, as a family of states.
  The model is a `ManyBody.SquareInteraction` with term bound `J` and Hermitian total sum.
* `pepsVector`: the native PEPS contraction in Euclidean coordinates.
* `HasPEPSApproximation`: a nonzero PEPS with specified bond and error bounds.
* `PolynomialPEPSApproximation`: the uniform source theorem as a proposition.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, Theorem 1.1, `eq:model`, `eq:global-gap`, `eq:target-error`.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open ManyBody (Edge SquareInteraction SquareLatticeVertex squareLatticeGraph)

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

open ManyBody (IsGapped groundSpace)

namespace TNLean.PEPS.Approximation

/-- Configuration coordinates on the original open square.
Source: polynomial-PEPS Section 1, the site Hilbert spaces. -/
abbrev Configuration (L q : ℕ) := SquareLatticeVertex L L → Fin q

/-- The physical Hilbert space of the open square.
Source: polynomial-PEPS Section 1. -/
abbrev StateSpace (L q : ℕ) := EuclideanSpace ℂ (Configuration L q)

/-- The states admitted by the model at local dimension `q`, term bound `J` and gap `Δ`: the
unit gapped ground vectors, with gap `Δ`, of the open-square Hamiltonians of side `L`: one
term on each site and one on each nearest-neighbor edge, each of norm at most `J`, with
Hermitian total sum. Individual terms need not be Hermitian. Source: polynomial-PEPS
`eq:model` and `eq:global-gap`. -/
def IsSquareGroundState (q : ℕ) (J Δ : ℝ) (L : ℕ) (Ω : StateSpace L q) : Prop :=
  ∃ h : SquareInteraction L q, h.hamiltonian.IsHermitian ∧ (∀ i, ‖h.term i‖ ≤ J) ∧
    ∃ E₀ : ℝ, ‖Ω‖ = 1 ∧ IsGapped h.hamiltonian E₀ Δ ∧
      groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω}

/-- A ground vector of the model is a unit vector. Source: polynomial-PEPS `eq:global-gap`. -/
theorem IsSquareGroundState.norm_eq_one {q : ℕ} {J Δ : ℝ} {L : ℕ} {Ω : StateSpace L q}
    (hΩ : IsSquareGroundState q J Δ L Ω) : ‖Ω‖ = 1 := by
  obtain ⟨_, _, _, _, hn, -, -⟩ := hΩ
  exact hn

/-- The contraction of a native PEPS, in Euclidean configuration coordinates.
Source: polynomial-PEPS Section 1, the unnormalized vector `Φ`. -/
noncomputable def pepsVector {L q : ℕ} (A : Tensor (squareLatticeGraph L L) q) :
    StateSpace L q :=
  (EuclideanSpace.equiv (Configuration L q) ℂ).symm (stateCoeff A)

/-- A nonzero native PEPS on the original graph, with positive bonds bounded
by `C L^c` and normalized global error at most `L⁻¹`, up to phase.
Source: polynomial-PEPS Theorem 1.1 and `eq:target-error`. -/
def HasPEPSApproximation (C c : ℝ) (L q : ℕ) (Ω : StateSpace L q) : Prop :=
  ∃ A : Tensor (squareLatticeGraph L L) q,
    (∀ e, 0 < A.bondDim e) ∧
    (∀ e, (A.bondDim e : ℝ) ≤ C * (L : ℝ) ^ c) ∧
    pepsVector A ≠ 0 ∧
    ∃ θ : ℝ,
      ‖((‖pepsVector A‖⁻¹ : ℝ) : ℂ) • pepsVector A -
        Complex.exp ((θ : ℂ) * Complex.I) • Ω‖ ≤ (L : ℝ)⁻¹

/-- The uniform polynomial-PEPS target, with constants chosen before the grid
size, Hamiltonian, and ground vector. Source: polynomial-PEPS Theorem 1.1 (`thm:main`).
The existential phase is equivalent to the printed minimum over phases by
`hasPEPSApproximation_iff_iInf`; no proof of the target is asserted here. -/
def PolynomialPEPSApproximation : Prop :=
  ∀ q : ℕ, 2 ≤ q → ∀ J Δ : ℝ, 0 < J → 0 < Δ →
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ L : ℕ, 2 ≤ L → ∀ h : SquareInteraction L q, h.hamiltonian.IsHermitian →
          (∀ i, ‖h.term i‖ ≤ J) →
        ∀ E₀ : ℝ, ∀ Ω : StateSpace L q,
          ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
          groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} → HasPEPSApproximation C c L q Ω

end TNLean.PEPS.Approximation

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.SquareLatticeGraph
import TNLean.Circuit.LocalCircuit
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The polynomial-bond PEPS approximation statement

The input is an open square-grid Hamiltonian. Only its total sum is required
to be Hermitian. The approximating tensor is a native graph PEPS on the same
edges, with positive edge dimensions and nonzero contraction. Error concerns
the normalized global vector, with a freely chosen phase.

## Main definitions

* `SquareHamiltonian`: bounded site and edge terms with Hermitian total sum.
* `pepsVector`: the native PEPS contraction in Euclidean coordinates.
* `HasPEPSApproximation`: a nonzero PEPS with specified bond and error bounds.
* `PolynomialPEPSApproximation`: the uniform source theorem as a proposition.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, Theorem 1.1, `eq:model`, `eq:global-gap`, `eq:target-error`.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript:
  preprints/
  Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/
  build/
  sections/
  00-introduction.tex
Labels: eq:global-gap.
Manuscript:
  preprints/
  Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/
  build/
  sections/
  00-introduction.tex
Labels: eq:model.
Manuscript:
  preprints/
  Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/
  build/
  sections/
  00-introduction.tex
Labels: thm:main.
Manuscript:
  preprints/
  Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/
  build/
  sections/
  00-introduction.tex
Labels: thm:main, eq:target-error.
Provenance-ID: 8738-tnlean.peps.approximation.configuration
Downstream declaration: TNLean.PEPS.Approximation.Configuration
Provenance-ID: 8738-tnlean.peps.approximation.statespace
Downstream declaration: TNLean.PEPS.Approximation.StateSpace
Provenance-ID: 8738-tnlean.peps.approximation.squarehamiltonian
Downstream declaration: TNLean.PEPS.Approximation.SquareHamiltonian
Provenance-ID: 8738-tnlean.peps.approximation.squarehamiltonian.operator
Downstream declaration: TNLean.PEPS.Approximation.SquareHamiltonian.operator
Provenance-ID: 8738-tnlean.peps.approximation.squarehamiltonian.isgappedgroundstate
Downstream declaration: TNLean.PEPS.Approximation.SquareHamiltonian.IsGappedGroundState
Provenance-ID: 8738-tnlean.peps.approximation.pepsvector
Downstream declaration: TNLean.PEPS.Approximation.pepsVector
Provenance-ID: 8738-tnlean.peps.approximation.haspepsapproximation
Downstream declaration: TNLean.PEPS.Approximation.HasPEPSApproximation
Provenance-ID: 8738-tnlean.peps.approximation.polynomialpepsapproximation
Downstream declaration: TNLean.PEPS.Approximation.PolynomialPEPSApproximation
-/

namespace TNLean.PEPS.Approximation

/-- Configuration coordinates on the original open square.
Source: polynomial-PEPS Section 1, the site Hilbert spaces. -/
abbrev Configuration (L q : ℕ) := SquareLatticeVertex L L → Fin q

/-- The physical Hilbert space of the open square.
Source: polynomial-PEPS Section 1. -/
abbrev StateSpace (L q : ℕ) := EuclideanSpace ℂ (Configuration L q)

/-- Bounded site and edge interactions whose total sum is Hermitian.
Individual terms need not be Hermitian. Source: polynomial-PEPS `eq:model`. -/
structure SquareHamiltonian (L q : ℕ) (J : ℝ) where
  /-- One operator for each site. -/
  siteTerm : SquareLatticeVertex L L → Matrix (Configuration L q) (Configuration L q) ℂ
  /-- One operator for each original nearest-neighbor edge. -/
  edgeTerm : Edge (squareLatticeGraph L L) →
    Matrix (Configuration L q) (Configuration L q) ℂ
  /-- Site operators act trivially off their designated site. -/
  site_supported : ∀ v, siteTerm v ∈ QuantumCircuit.supportedOperators q {v}
  /-- Edge operators act trivially off their two designated endpoints. -/
  edge_supported : ∀ e, edgeTerm e ∈
    QuantumCircuit.supportedOperators q {e.1.1, e.1.2}
  /-- The site-term bound uses the Euclidean operator norm. -/
  site_norm_le : ∀ v, ‖siteTerm v‖ ≤ J
  /-- The edge-term bound uses the Euclidean operator norm. -/
  edge_norm_le : ∀ e, ‖edgeTerm e‖ ≤ J
  /-- Hermiticity is imposed on the total Hamiltonian alone. -/
  hermitian : ((∑ v, siteTerm v) + ∑ e, edgeTerm e).IsHermitian

/-- The total open-square Hamiltonian.
Source: polynomial-PEPS `eq:model`. -/
noncomputable def SquareHamiltonian.operator {L q : ℕ} {J : ℝ}
    (h : SquareHamiltonian L q J) : Matrix (Configuration L q) (Configuration L q) ℂ :=
  (∑ v, h.siteTerm v) + ∑ e, h.edgeTerm e

/-- Unit eigenvector and the full-system projector gap on the open square.
Source: polynomial-PEPS `eq:global-gap`; uniqueness follows for positive `Δ`. -/
def SquareHamiltonian.IsGappedGroundState {L q : ℕ} {J : ℝ}
    (h : SquareHamiltonian L q J) (E₀ : ℝ) (Ω : StateSpace L q) (Δ : ℝ) : Prop :=
  ‖Ω‖ = 1 ∧
    Matrix.toEuclideanCLM (n := Configuration L q) (𝕜 := ℂ) h.operator Ω = (E₀ : ℂ) • Ω ∧
      (h.operator - (E₀ : ℂ) • 1 - (Δ : ℂ) •
        (1 - Matrix.vecMulVec (fun x ↦ Ω x) (star (fun x ↦ Ω x)))).PosSemidef

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
The existential phase formulation is to be related to the printed minimum
by the phase-minimizer theorem; no proof of the target is asserted here. -/
def PolynomialPEPSApproximation : Prop :=
  ∀ q : ℕ, 2 ≤ q → ∀ J Δ : ℝ, 0 < J → 0 < Δ →
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ L : ℕ, 2 ≤ L → ∀ h : SquareHamiltonian L q J,
        ∀ E₀ : ℝ, ∀ Ω : StateSpace L q,
          h.IsGappedGroundState E₀ Ω Δ → HasPEPSApproximation C c L q Ω

end TNLean.PEPS.Approximation

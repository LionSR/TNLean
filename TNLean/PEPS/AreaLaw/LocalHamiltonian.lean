/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.FiniteDomain
import TNLean.Circuit.SiteEmbedding
import TNLean.Algebra.GappedGroundState
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Finite-range Hamiltonians on induced lattice domains

The interaction family has one term for each nonempty support of bounded
induced-graph diameter. A term may be zero. Support is expressed using the
existing algebra of operators acting trivially outside a region. Norms are
Euclidean operator norms, rather than entrywise matrix norms.

## Main definitions

* `LocalHamiltonian`: the bounded Hermitian interaction family.
* `LocalHamiltonian.operator`: its finite sum.
* `IsGappedGroundState`: a unit eigenvector and the full-system projector gap.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `eq:hamiltonian` and Theorem 1.1.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder

namespace TNLean.PEPS.AreaLaw

/-- The physical Hilbert space in configuration coordinates.
Source: area-law Section 1, the tensor product of the site spaces. -/
abbrev StateSpace (Λ : Finset (ℤ × ℤ)) (q : ℕ) :=
  EuclideanSpace ℂ (Configuration Λ q)

/-- One bounded Hermitian operator per nonempty admissible support.
Source: area-law `eq:hamiltonian`. -/
structure LocalHamiltonian (Λ : Finset (ℤ × ℤ)) (q R : ℕ) (J : ℝ) where
  /-- The term assigned to each support; zero terms are permitted. -/
  term : AdmissibleSupport Λ R → Matrix (Configuration Λ q) (Configuration Λ q) ℂ
  /-- Each term acts trivially on the complementary sites. -/
  supported : ∀ X, term X ∈ QuantumCircuit.supportedOperators q (X.1 : Set (Site Λ))
  /-- Each summand is Hermitian, as required by `eq:hamiltonian`. -/
  hermitian : ∀ X, (term X).IsHermitian
  /-- Each summand has Euclidean operator norm at most `J`. -/
  norm_le : ∀ X, ‖term X‖ ≤ J

/-- The finite sum over distinct admissible supports.
Source: area-law `eq:hamiltonian`. -/
noncomputable def LocalHamiltonian.operator {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J : ℝ}
    (h : LocalHamiltonian Λ q R J) : Matrix (Configuration Λ q) (Configuration Λ q) ℂ :=
  ∑ X, h.term X

/-- The interaction sum is Hermitian. -/
theorem LocalHamiltonian.operator_isHermitian {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J : ℝ}
    (h : LocalHamiltonian Λ q R J) : h.operator.IsHermitian := by
  change (∑ X, h.term X)ᴴ = ∑ X, h.term X
  simp only [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl fun X _ ↦ h.hermitian X

/-- The zero interaction family, which is also defined for empty domains.
Source: area-law `eq:hamiltonian`, zero summands are permitted. -/
noncomputable def LocalHamiltonian.zero (Λ : Finset (ℤ × ℤ)) (q R : ℕ)
    (J : ℝ) (hJ : 0 ≤ J) : LocalHamiltonian Λ q R J where
  term _ := 0
  supported _ := Submodule.zero_mem _
  hermitian _ := Matrix.isHermitian_zero
  norm_le _ := by simpa using hJ

/-- Place a local matrix on a region, with identity on its complement.
This is the existing circuit embedding specialized to the domain sites.
Source: area-law Section 1, the definition of a supported operator. -/
noncomputable def localLift (Λ : Finset (ℤ × ℤ)) (q : ℕ) (X : Finset (Site Λ))
    (K : Matrix (↥X → Fin q) (↥X → Fin q) ℂ) :
    Matrix (Configuration Λ q) (Configuration Λ q) ℂ :=
  QuantumCircuit.embedOp (fun x : ↥X ↦ x.val) K

/-- A placed local matrix belongs to the existing supported-operator algebra. -/
theorem localLift_mem_supportedOperators (Λ : Finset (ℤ × ℤ)) (q : ℕ)
    (X : Finset (Site Λ)) (K : Matrix (↥X → Fin q) (↥X → Fin q) ℂ) :
    localLift Λ q X K ∈ QuantumCircuit.supportedOperators q (X : Set (Site Λ)) := by
  simpa [localLift] using
    QuantumCircuit.embedOp_mem_supportedOperators
      (e := fun x : ↥X ↦ x.val) Subtype.val_injective K

/-- A unit eigenvector with the full-system projector gap, the specialization of
`Matrix.IsGappedGroundState` to the finite-domain state space.
Source: area-law Theorem 1.1. For a Hermitian Hamiltonian and positive `Δ`,
the inequality also forces the eigenvalue to be the ground energy and its
eigenspace to be one-dimensional; these consequences are separate proof obligations. -/
def IsGappedGroundState (Λ : Finset (ℤ × ℤ)) (q : ℕ)
    (H : Matrix (Configuration Λ q) (Configuration Λ q) ℂ)
    (E₀ : ℝ) (Ω : StateSpace Λ q) (Δ : ℝ) : Prop :=
  Matrix.IsGappedGroundState H E₀ Ω Δ

end TNLean.PEPS.AreaLaw

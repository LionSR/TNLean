/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.FiniteDomain
import TNLean.Circuit.SiteEmbedding
import Mathlib.Analysis.CStarAlgebra.Matrix
import QICLean.ManyBody.Hamiltonian.Models

/-!
# Finite-range Hamiltonians on induced lattice domains

A finite-range Hamiltonian is an interaction `ManyBody.PlaneInteraction Λ q R`, with one term
for each nonempty support of bounded induced-graph diameter, whose terms are Hermitian and of
norm at most `J`; both are hypotheses of the statements that use them. A term may be zero. Support
is expressed using the
existing algebra of operators acting trivially outside a region. Norms are
Euclidean operator norms, rather than entrywise matrix norms.

## Main definitions

* `localLift`: a local matrix placed on a region, with identity on its complement.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `eq:hamiltonian` and Theorem 1.1.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder

open ManyBody (AdmissibleSupport)

namespace TNLean.Lattice

/-- The physical Hilbert space in configuration coordinates.
Source: area-law Section 1, the tensor product of the site spaces. -/
abbrev StateSpace (Λ : Finset (ℤ × ℤ)) (q : ℕ) :=
  EuclideanSpace ℂ (Configuration Λ q)

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
    localLift Λ q X K ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) X := by
  simpa [localLift] using
    QuantumCircuit.embedOp_mem_supportedOperators
      (e := fun x : ↥X ↦ x.val) Subtype.val_injective K

end TNLean.Lattice

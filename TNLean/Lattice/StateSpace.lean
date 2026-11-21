/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.FiniteDomain
import QICLean.ManyBody.Sites.PlacedConfiguration
import Mathlib.Analysis.CStarAlgebra.Matrix
import QICLean.ManyBody.Hamiltonian.Models

/-!
# The physical Hilbert space of a finite lattice domain

The physical Hilbert space of a finite set `Λ ⊂ ℤ²` of sites with local dimension `q`, in
configuration coordinates. A finite-range Hamiltonian on `Λ` is an interaction
`ManyBody.PlaneInteraction Λ q R`, with one term for each nonempty support of bounded
induced-graph diameter, whose terms are Hermitian and of norm at most `J`; both are hypotheses
of the statements that use them, and norms are Euclidean operator norms.

## Main definitions

* `StateSpace`: the physical Hilbert space in configuration coordinates.

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

end TNLean.Lattice

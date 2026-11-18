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

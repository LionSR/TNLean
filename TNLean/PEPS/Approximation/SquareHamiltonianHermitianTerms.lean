/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.Basic
import TNLean.PEPS.Approximation.SquareGridContraction
import TNLean.Lattice.MarginalTails
import QICLean.Algebra.HermitianPartSum
import Mathlib.Analysis.Complex.Basic

/-!
# Hermitian local terms of the original square Hamiltonian

Replace every site and edge term by its Hermitian part. Their supports and
norm bounds are preserved, and their sum is the original Hamiltonian,
since only that total was assumed Hermitian. Forward edges retain their
original ordered endpoints under the native square-grid identification.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, September 24, 2026, `00-introduction.tex`, lines 39–44, `eq:model`,
and `03-patches.tex`, lines 214–333, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open ManyBody (SquareLatticeSiteOrEdge squareLatticeSiteOrEdgeSupport)

open Matrix ComplexStarModule
open scoped Matrix.Norms.L2Operator

noncomputable section

open TNLean.Lattice

namespace TNLean.PEPS.Approximation

private def squareInteractionTerm {L q : ℕ} {J : ℝ} (h : SquareHamiltonian L q J) :
    SquareLatticeSiteOrEdge L L → Matrix (Configuration L q) (Configuration L q) ℂ
  | .inl v => h.siteTerm v
  | .inr e => h.edgeTerm e

/-- The Hermitian part of each original interaction. Source:
`00-introduction.tex`, lines 39–44; `03-patches.tex`, lines 214–333. -/
def SquareHamiltonian.hermitianTerm {L q : ℕ} {J : ℝ} (h : SquareHamiltonian L q J)
    (i : SquareLatticeSiteOrEdge L L) : Matrix (Configuration L q) (Configuration L q) ℂ :=
  ℜ (squareInteractionTerm h i)

/-- The Hermitian part of an original interaction remains in its designated
circuit supported-operator algebra, since that algebra is closed under
adjoints and real linear combinations. Source: `00-introduction.tex`, `eq:model`. -/
theorem SquareHamiltonian.hermitianTerm_mem_supportedOperators {L q : ℕ} {J : ℝ}
    (h : SquareHamiltonian L q J) (i : SquareLatticeSiteOrEdge L L) :
    h.hermitianTerm i ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
      (squareLatticeSiteOrEdgeSupport i : Finset (Vertex L)) := by
  have hs : squareInteractionTerm h i ∈
      ManyBody.supportedOperators (fun _ ↦ Fin q) (squareLatticeSiteOrEdgeSupport i : Finset (Vertex L)) := by
    cases i with
    | inl v =>
      simpa only [squareInteractionTerm, squareLatticeSiteOrEdgeSupport, Finset.coe_singleton]
        using h.site_supported v
    | inr e =>
      simpa only [squareInteractionTerm, squareLatticeSiteOrEdgeSupport, Finset.coe_insert,
        Finset.coe_singleton]
        using h.edge_supported e
  exact coe_realPart_mem_of_star_mem
    (S := (Subalgebra.toSubmodule (ManyBody.supportedOperators (fun _ ↦ Fin q)
      (squareLatticeSiteOrEdgeSupport i : Finset (Vertex L))).toSubalgebra).restrictScalars ℝ)
    hs (show star _ ∈ ManyBody.supportedOperators _ _ from star_mem hs)

/-- Hermitian replacement preserves the original interaction support.
Source: `00-introduction.tex`, `eq:model`. -/
theorem SquareHamiltonian.hermitianTerm_supported {L q : ℕ} {J : ℝ}
    (h : SquareHamiltonian L q J) (i : SquareLatticeSiteOrEdge L L) :
    Entropy.IsSupportedOn (n := fun _ : Vertex L => q)
      (h.hermitianTerm i) (squareLatticeSiteOrEdgeSupport i) :=
  (h.hermitianTerm_mem_supportedOperators i)

/-- Every replaced interaction is Hermitian. Source:
`00-introduction.tex`, `eq:model`. -/
theorem SquareHamiltonian.hermitianTerm_isHermitian {L q : ℕ} {J : ℝ}
    (h : SquareHamiltonian L q J) (i : SquareLatticeSiteOrEdge L L) :
    (h.hermitianTerm i).IsHermitian :=
  (ℜ (squareInteractionTerm h i)).property.isHermitian

/-- The original norm bound holds without any factor loss. Source:
`00-introduction.tex`, `eq:model`. -/
theorem SquareHamiltonian.hermitianTerm_norm_le {L q : ℕ} {J : ℝ}
    (h : SquareHamiltonian L q J) (i : SquareLatticeSiteOrEdge L L) :
    ‖h.hermitianTerm i‖ ≤ J := by
  apply (realPart.norm_le (squareInteractionTerm h i)).trans
  cases i with
  | inl v => exact h.site_norm_le v
  | inr e => exact h.edge_norm_le e

/-- Hermitian replacement recovers exactly the original Hamiltonian.
Only total Hermiticity is used. Source: `00-introduction.tex`, `eq:model`. -/
theorem SquareHamiltonian.sum_hermitianTerm {L q : ℕ} {J : ℝ}
    (h : SquareHamiltonian L q J) :
    (∑ i : SquareLatticeSiteOrEdge L L, h.hermitianTerm i) = h.operator := by
  have hsum : (∑ i : SquareLatticeSiteOrEdge L L, squareInteractionTerm h i) = h.operator := by
    rw [Fintype.sum_sum_type]
    change (∑ v, h.siteTerm v) + (∑ e, h.edgeTerm e) = _
    rfl
  have hh : IsSelfAdjoint (∑ i : SquareLatticeSiteOrEdge L L, squareInteractionTerm h i) := by
    rw [hsum]
    exact h.hermitian.isSelfAdjoint
  exact (sum_coe_realPart_of_isSelfAdjoint Finset.univ (squareInteractionTerm h) hh).trans hsum

end TNLean.PEPS.Approximation

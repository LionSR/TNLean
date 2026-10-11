/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.Basic
import TNLean.PEPS.Approximation.SquareGridContraction
import TNLean.PEPS.AreaLaw.MarginalTails
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

open Classical Matrix ComplexStarModule
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace TNLean.PEPS.Approximation

/-- The site and nearest-neighbor interaction labels of the original
Hamiltonian. Source: `00-introduction.tex`, `eq:model`. -/
abbrev SquareInteraction (L : ℕ) := Vertex L ⊕ ForwardEdge L

/-- The original one-site or two-site support. Source:
`00-introduction.tex`, `eq:model`. -/
def squareInteractionSupport {L : ℕ} : SquareInteraction L → Finset (Vertex L)
  | .inl v => {v}
  | .inr e => {e.val.1, e.val.2}

private def squareInteractionTerm {L q : ℕ} {J : ℝ} (h : SquareHamiltonian L q J) :
    SquareInteraction L → Matrix (Configuration L q) (Configuration L q) ℂ
  | .inl v => h.siteTerm v
  | .inr e => h.edgeTerm (forwardSquareEdgeEquiv L e)

/-- The Hermitian part of each original interaction. Source:
`00-introduction.tex`, lines 39–44; `03-patches.tex`, lines 214–333. -/
def SquareHamiltonian.hermitianTerm {L q : ℕ} {J : ℝ} (h : SquareHamiltonian L q J)
    (i : SquareInteraction L) : Matrix (Configuration L q) (Configuration L q) ℂ :=
  ℜ (squareInteractionTerm h i)

/-- Hermitian replacement preserves the original interaction support.
Source: `00-introduction.tex`, `eq:model`. -/
theorem SquareHamiltonian.hermitianTerm_supported {L q : ℕ} {J : ℝ}
    (h : SquareHamiltonian L q J) (i : SquareInteraction L) :
    Entropy.IsSupportedOn (n := fun _ : Vertex L => q)
      (h.hermitianTerm i) (squareInteractionSupport i) := by
  have hs : squareInteractionTerm h i ∈
      QuantumCircuit.supportedOperators q (squareInteractionSupport i : Set (Vertex L)) := by
    cases i with
    | inl v =>
      simpa only [squareInteractionTerm, squareInteractionSupport, Finset.coe_singleton]
        using h.site_supported v
    | inr e =>
      simpa only [squareInteractionTerm, squareInteractionSupport, Finset.coe_insert,
        Finset.coe_singleton, forwardSquareEdgeEquiv_val]
        using h.edge_supported (forwardSquareEdgeEquiv L e)
  apply QuantumCircuit.isSupportedOn_of_mem_supportedOperators
  exact coe_realPart_mem_of_star_mem
    (S := (QuantumCircuit.supportedOperators q
      (squareInteractionSupport i : Set (Vertex L))).restrictScalars ℝ)
    hs (QuantumCircuit.star_mem_supportedOperators hs)

/-- Every replaced interaction is Hermitian. Source:
`00-introduction.tex`, `eq:model`. -/
theorem SquareHamiltonian.hermitianTerm_isHermitian {L q : ℕ} {J : ℝ}
    (h : SquareHamiltonian L q J) (i : SquareInteraction L) :
    (h.hermitianTerm i).IsHermitian :=
  (ℜ (squareInteractionTerm h i)).property.isHermitian

/-- The original norm bound holds without any factor loss. Source:
`00-introduction.tex`, `eq:model`. -/
theorem SquareHamiltonian.hermitianTerm_norm_le {L q : ℕ} {J : ℝ}
    (h : SquareHamiltonian L q J) (i : SquareInteraction L) :
    ‖h.hermitianTerm i‖ ≤ J := by
  apply (realPart.norm_le (squareInteractionTerm h i)).trans
  cases i with
  | inl v => exact h.site_norm_le v
  | inr e => exact h.edge_norm_le (forwardSquareEdgeEquiv L e)

/-- Hermitian replacement recovers exactly the original Hamiltonian.
Only total Hermiticity is used. Source: `00-introduction.tex`, `eq:model`. -/
theorem SquareHamiltonian.sum_hermitianTerm {L q : ℕ} {J : ℝ}
    (h : SquareHamiltonian L q J) :
    (∑ i : SquareInteraction L, h.hermitianTerm i) = h.operator := by
  have hsum : (∑ i : SquareInteraction L, squareInteractionTerm h i) = h.operator := by
    rw [Fintype.sum_sum_type]
    change (∑ v, h.siteTerm v) + (∑ e, h.edgeTerm (forwardSquareEdgeEquiv L e)) = _
    rw [(forwardSquareEdgeEquiv L).sum_comp h.edgeTerm]
    rfl
  have hh : IsSelfAdjoint (∑ i : SquareInteraction L, squareInteractionTerm h i) := by
    rw [hsum]
    exact h.hermitian.isSelfAdjoint
  exact (sum_coe_realPart_of_isSelfAdjoint Finset.univ (squareInteractionTerm h) hh).trans hsum

end TNLean.PEPS.Approximation

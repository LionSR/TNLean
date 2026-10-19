/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SquareInteractionSupport

/-!
# Nearest-neighbor terms of the original square Hamiltonian

The original site and edge terms, replaced by their Hermitian parts and
transported to the integer rectangle, form a nearest-neighbor interaction
family with the same bound and the same total Hamiltonian.

Source: polynomial-PEPS manuscript, `00-introduction.tex`, `eq:model`, and
`03-patches.tex`, lines 213–336; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped BigOperators Matrix.Norms.L2Operator

namespace TNLean.PEPS.Approximation

/-- The original Hamiltonian is a sum of bounded Hermitian terms on the actual
singleton and nearest-neighbor supports in the integer rectangle.
Source: polynomial-PEPS `eq:model` and `03-patches.tex`, lines 213–336. -/
theorem SquareHamiltonian.exists_nearestNeighbor_terms {L q : ℕ} {J : ℝ}
    (h : SquareHamiltonian L q J) (hJ : 0 ≤ J)
    [LinearOrder (Lattice.Site (AreaLaw.rectangularDomain L L))] :
    ∃ T : (Lattice.Site (AreaLaw.rectangularDomain L L) ⊕
        Edge (Lattice.domainGraph (AreaLaw.rectangularDomain L L))) →
        Matrix (Lattice.Configuration (AreaLaw.rectangularDomain L L) q)
          (Lattice.Configuration (AreaLaw.rectangularDomain L L) q) ℂ,
      (∀ i, Entropy.IsSupportedOn
        (n := fun _ : Lattice.Site (AreaLaw.rectangularDomain L L) ↦ q)
        (T i) (AreaLaw.nearestNeighborSupport i)) ∧
      (∀ i, (T i).IsHermitian) ∧ (∀ i, ‖T i‖ ≤ J) ∧
      (∑ i, T i) = (h.toAreaLawHamiltonian hJ).operator := by
  let e := Equiv.sumCongr (AreaLaw.rectangleSiteEquiv L L)
    ((forwardSquareEdgeEquiv L).trans (Edge.equiv (AreaLaw.rectangleGraphIso L L)))
  let cfg := AreaLaw.rectangleConfigurationEquiv L L q
  refine ⟨fun i ↦ Matrix.reindex cfg cfg (h.hermitianTerm (e.symm i)), ?_, ?_, ?_, ?_⟩
  · intro i
    have hs := QuantumCircuit.embedOp_mem_supportedOperators_image
      (AreaLaw.rectangleSiteEquiv L L).injective
      (h.hermitianTerm_mem_supportedOperators (e.symm i))
    rw [embedOp_rectangle_eq_reindex] at hs
    have hi : (squareAreaLawSupport L (e.symm i)).val =
        AreaLaw.nearestNeighborSupport i := by
      simpa only [e, Equiv.apply_symm_apply] using
        squareAreaLawSupport_val_eq_nearestNeighborSupport L (e.symm i)
    apply QuantumCircuit.isSupportedOn_of_mem_supportedOperators
    simpa only [← hi, cfg, squareAreaLawSupport, Finset.coe_image] using hs
  · exact fun i ↦ (h.hermitianTerm_isHermitian (e.symm i)).reindex cfg
  · exact fun i ↦ (Matrix.l2_opNorm_reindex_equiv cfg (h.hermitianTerm (e.symm i))).le.trans
      (h.hermitianTerm_norm_le (e.symm i))
  · exact calc
      _ = ∑ j : SquareInteraction L, Matrix.reindex cfg cfg (h.hermitianTerm j) :=
        e.symm.sum_comp _
      _ = Matrix.reindex cfg cfg (∑ j : SquareInteraction L, h.hermitianTerm j) :=
        (map_sum (Matrix.reindexAlgEquiv ℂ ℂ cfg) h.hermitianTerm Finset.univ).symm
      _ = Matrix.reindex cfg cfg h.operator :=
        congrArg (Matrix.reindex cfg cfg) h.sum_hermitianTerm
      _ = _ := (h.toAreaLawHamiltonian_operator hJ).symm

end TNLean.PEPS.Approximation

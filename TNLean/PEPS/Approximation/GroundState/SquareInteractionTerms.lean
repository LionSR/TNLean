/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Hamiltonian.RectangleInteraction
import TNLean.PEPS.Tensor.SquareLattice.Basic
import TNLean.PEPS.Tensor.SquareLattice.SquareGridContraction
import QICLean.ManyBody.Sites.Lattice.NearestNeighborCrossing
import TNLean.PEPS.Tensor.Network.IsoTransport

/-!
# Original interaction supports in the integer rectangle

The bijection from original site and forward-edge labels to rectangle sites
and unordered edges preserves their designated supports. The order chosen
for rectangle sites affects only the representative of each unordered edge.

Source: polynomial-PEPS `00-introduction.tex`, `eq:model`, and
`03-patches.tex`, lines 213–336; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

## Nearest-neighbor terms of the original square Hamiltonian

The original site and edge terms, replaced by their Hermitian parts and
transported to the integer rectangle, form a nearest-neighbor interaction
family with the same bound and the same total Hamiltonian.

Source: polynomial-PEPS manuscript, `00-introduction.tex`, `eq:model`, and
`03-patches.tex`, lines 213–336; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

section

open ManyBody (SquareLatticeSiteOrEdge squareLatticeSiteOrEdgeSupport)

namespace TNLean.PEPS.Approximation

/-- Relabelling the original sites and forward edges gives precisely the
nearest-neighbor supports in the integer rectangle.
Source: polynomial-PEPS `eq:model` and `03-patches.tex`, lines 213–336. -/
theorem rectangleSupport_val_eq_nearestNeighborSupport (L : ℕ)
    [LinearOrder ↥(ManyBody.rectangularDomain L L)]
    (i : SquareLatticeSiteOrEdge L L) :
    let e := Equiv.sumCongr (ManyBody.rectangleSiteEquiv L L)
      (ManyBody.Edge.equiv (ManyBody.rectangleGraphIso L L))
    (ManyBody.rectangleSupport i).val = ManyBody.nearestNeighborSupport (e i) := by
  rcases i with v | e <;>
    simp only [ManyBody.rectangleSupport, squareLatticeSiteOrEdgeSupport,
      ManyBody.nearestNeighborSupport, Finset.map_singleton, Finset.map_insert,
      Equiv.toEmbedding_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Sum.elim_inl,
      Sum.elim_inr, ManyBody.Edge.equiv_apply]
  exact (Finset.coe_injective
    (Finset.coe_pair.trans
      ((Set.pair_eq_pair_iff.mpr
        (ManyBody.Edge.map_endpoints (ManyBody.rectangleGraphIso L L)
          e)).trans Finset.coe_pair.symm))).symm

end TNLean.PEPS.Approximation

end

section

open ManyBody (Edge SquareLatticeSiteOrEdge SquareInteraction)

open scoped BigOperators Matrix.Norms.L2Operator

namespace TNLean.PEPS.Approximation

/-- The original Hamiltonian is a sum of bounded Hermitian terms on the actual
singleton and nearest-neighbor supports in the integer rectangle.
Source: polynomial-PEPS `eq:model` and `03-patches.tex`, lines 213–336. -/
theorem _root_.ManyBody.SquareInteraction.exists_nearestNeighbor_terms {L q : ℕ} {J : ℝ}
    (h : SquareInteraction L q) (hh : h.hamiltonian.IsHermitian) (hhJ : ∀ i, ‖h.term i‖ ≤ J)
    [LinearOrder ↥(ManyBody.rectangularDomain L L)] :
    ∃ T : (↥(ManyBody.rectangularDomain L L) ⊕
        Edge (ManyBody.planeDomainGraph (ManyBody.rectangularDomain L L))) →
        Matrix (↥(ManyBody.rectangularDomain L L) → Fin q)
          (↥(ManyBody.rectangularDomain L L) → Fin q) ℂ,
      (∀ i, ManyBody.IsSupportedOn
        (X := fun _ ↦ Fin q)
        (T i) (ManyBody.nearestNeighborSupport i)) ∧
      (∀ i, (T i).IsHermitian) ∧ (∀ i, ‖T i‖ ≤ J) ∧
      (∑ i, T i) =
        (ManyBody.RectangleInteraction.toPlaneInteraction h.hermitianPart).hamiltonian := by
  let e := Equiv.sumCongr (ManyBody.rectangleSiteEquiv L L)
    (ManyBody.Edge.equiv (ManyBody.rectangleGraphIso L L))
  let cfg := ManyBody.rectangleConfigurationEquiv L L q
  refine ⟨fun i ↦ Matrix.reindex cfg cfg (h.hermitianPart.term (e.symm i)), ?_, ?_, ?_, ?_⟩
  · intro i
    have hi : (ManyBody.rectangleSupport (e.symm i)).val = ManyBody.nearestNeighborSupport i := by
      simpa only [e, Equiv.apply_symm_apply] using
        rectangleSupport_val_eq_nearestNeighborSupport L (e.symm i)
    have hs := ManyBody.reindex_siteConfigurationEquiv_mem_supportedOperators
      (X := fun _ : ManyBody.SquareLatticeVertex L L ↦ Fin q)
      (X' := fun _ : ↥(ManyBody.rectangularDomain L L) ↦ Fin q)
      (ManyBody.rectangleSiteEquiv L L) (fun _ ↦ Equiv.refl (Fin q))
      (D' := (ManyBody.rectangleSupport (e.symm i)).val)
      (fun v ↦ (ManyBody.mem_rectangleSupport_iff (e.symm i) v).symm)
      (h.hermitianPart.mem (e.symm i))
    rw [ManyBody.siteConfigurationEquiv_rectangleSiteEquiv, hi] at hs
    change _ ∈ ManyBody.supportedOperators _ _
    exact hs
  · exact fun i ↦ (h.isHermitian_hermitianPart_term (e.symm i)).reindex cfg
  · exact fun i ↦ (Matrix.l2_opNorm_reindex_equiv cfg (h.hermitianPart.term (e.symm i))).le.trans
      ((h.norm_hermitianPart_term_le (e.symm i)).trans (hhJ (e.symm i)))
  · exact calc
      _ = ∑ j : SquareLatticeSiteOrEdge L L, Matrix.reindex cfg cfg (h.hermitianPart.term j) :=
        e.symm.sum_comp _
      _ = Matrix.reindex cfg cfg (∑ j : SquareLatticeSiteOrEdge L L, h.hermitianPart.term j) :=
        (map_sum (Matrix.reindexAlgEquiv ℂ ℂ cfg) h.hermitianPart.term Finset.univ).symm
      _ = Matrix.reindex cfg cfg h.hamiltonian :=
        congrArg (Matrix.reindex cfg cfg) (h.hamiltonian_hermitianPart hh)
      _ = _ := (h.hamiltonian_toPlaneInteraction_hermitianPart hh).symm

end TNLean.PEPS.Approximation

end

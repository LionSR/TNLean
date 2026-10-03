/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TwoPlaquetteGeometry
import TNLean.PEPS.VerticalTwoPlaquetteGeometry
import TNLean.PEPS.TorusVerticalFluxMove
import TNLean.PEPS.TranslatedTwoPlaquetteGeometry
import TNLean.PEPS.RegularInternalGaugeTransport
/-!
# Seven-edge determination of an embedded two-plaquette block
An isomorphism onto an induced region transports the seven edges of the
six-vertex two-plaquette graph to every internal bond. Directed equality on
these seven edges therefore determines the full internal assignment. This is
an auxiliary finite-block fact for SCP10, Theorem 6.16, lines 2271–2305.
-/
namespace TNLean.PEPS
private theorem edge_cases {i j : Fin 6} (hij : i < j)
    (hadj : twoPlaquetteGraph.Adj i j) :
    (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 5) ∨ (i = 1 ∧ j = 2) ∨
    (i = 1 ∧ j = 4) ∨ (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 5) := by
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals first
    | exact False.elim ((by decide : ¬ twoPlaquetteGraph.Adj _ _) hadj)
    | decide
variable {V : Type*} [LinearOrder V] {Γ : SimpleGraph V}
variable {G : Type*} [Group G]
/-- Seven mapped transports determine every internal ordered coefficient.
Source: SCP10, the elementary two-plaquette block, lines 2271–2305. -/
theorem twoPlaquette_internal_eq_of_edgeTransports (R : Finset V)
    (φ : twoPlaquetteGraph ≃g Γ.induce (R : Set V)) (u w : Edge Γ → G)
    (hL : regularDirectedTransport u
      (SimpleGraph.induce_adj.mp (φ.map_rel_iff'.mpr (by decide : twoPlaquetteGraph.Adj 0 1))) =
      regularDirectedTransport w
      (SimpleGraph.induce_adj.mp (φ.map_rel_iff'.mpr (by decide : twoPlaquetteGraph.Adj 0 1))))
    (hB : regularDirectedTransport u
      (SimpleGraph.induce_adj.mp (φ.map_rel_iff'.mpr (by decide : twoPlaquetteGraph.Adj 0 5))) =
      regularDirectedTransport w
      (SimpleGraph.induce_adj.mp (φ.map_rel_iff'.mpr (by decide : twoPlaquetteGraph.Adj 0 5))))
    (hU : regularDirectedTransport u
      (SimpleGraph.induce_adj.mp (φ.map_rel_iff'.mpr (by decide : twoPlaquetteGraph.Adj 1 2))) =
      regularDirectedTransport w
      (SimpleGraph.induce_adj.mp (φ.map_rel_iff'.mpr (by decide : twoPlaquetteGraph.Adj 1 2))))
    (hM : regularDirectedTransport u
      (SimpleGraph.induce_adj.mp (φ.map_rel_iff'.mpr (by decide : twoPlaquetteGraph.Adj 1 4))) =
      regularDirectedTransport w
      (SimpleGraph.induce_adj.mp (φ.map_rel_iff'.mpr (by decide : twoPlaquetteGraph.Adj 1 4))))
    (hT : regularDirectedTransport u
      (SimpleGraph.induce_adj.mp (φ.map_rel_iff'.mpr (by decide : twoPlaquetteGraph.Adj 2 3))) =
      regularDirectedTransport w
      (SimpleGraph.induce_adj.mp (φ.map_rel_iff'.mpr (by decide : twoPlaquetteGraph.Adj 2 3))))
    (hV : regularDirectedTransport u
      (SimpleGraph.induce_adj.mp (φ.map_rel_iff'.mpr (by decide : twoPlaquetteGraph.Adj 3 4))) =
      regularDirectedTransport w
      (SimpleGraph.induce_adj.mp (φ.map_rel_iff'.mpr (by decide : twoPlaquetteGraph.Adj 3 4))))
    (hR : regularDirectedTransport u
      (SimpleGraph.induce_adj.mp (φ.map_rel_iff'.mpr (by decide : twoPlaquetteGraph.Adj 4 5))) =
      regularDirectedTransport w
      (SimpleGraph.induce_adj.mp (φ.map_rel_iff'.mpr (by decide : twoPlaquetteGraph.Adj 4 5))))
    (e : Edge Γ) (he : e.1.1 ∈ R ∧ e.1.2 ∈ R) : u e = w e := by
  let e₀ := (Edge.equiv φ).symm ((inducedRegionEdgeEquiv R).symm ⟨e, he⟩)
  have hf : inducedRegionEdgeEquiv R (Edge.equiv φ e₀) = ⟨e, he⟩ := by
    simp only [e₀, Equiv.apply_symm_apply]
  have ha : Γ.Adj (φ e₀.1.1).1 (φ e₀.1.2).1 :=
    SimpleGraph.induce_adj.mp (φ.map_rel_iff'.mpr e₀.2.2)
  have hedge : Edge.ofAdj ha = e := by
    have hm : Edge.ofAdj ha = (inducedRegionEdgeEquiv R (Edge.equiv φ e₀)).1 := by
      apply Edge.ofAdj_eq_of_endpoints
      rcases Edge.map_endpoints φ e₀ with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
      · exact Or.inl ⟨(congrArg Subtype.val ha').symm, (congrArg Subtype.val hb').symm⟩
      · exact Or.inr ⟨(congrArg Subtype.val hb').symm, (congrArg Subtype.val ha').symm⟩
    exact hm.trans (congrArg Subtype.val hf)
  rw [← hedge]
  apply regularDirectedTransport_injective_on_edge ha
  rcases e₀ with ⟨⟨i, j⟩, hij, hadj⟩
  rcases edge_cases hij hadj with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hL
  · exact hB
  · exact hU
  · exact hM
  · exact hT
  · exact hV
  · exact hR
section
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (3 < height)]
local instance verticalTableWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance verticalTableHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 3 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
/-- All vertical traversals have identity transport in the native horizontal-bond insertion.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem torusVerticalFluxAssignment_up_transport (p q : X) (b : Bool) (l : G) :
    regularDirectedTransport (torusVerticalFluxAssignment p b l)
      (torusGraph_adj_up q.1 q.2) = 1 := by
  have hn (y : ZMod height) : Edge.ofAdj (torusGraph_adj_up q.1 q.2) ≠
      Edge.ofAdj (torusGraph_adj_right p.1 y) := by
    refine Edge.ofAdj_ne_of_endpoint_coordinates (torusGraph_adj_up q.1 q.2)
      (torusGraph_adj_right p.1 y) Prod.snd rfl ?_
    by_cases h : q.2 = y
    · right
      simp [h]
    · exact Or.inl h
  simp [regularDirectedTransport, torusVerticalFluxAssignment, hn]
/-- A rightward traversal outside the two selected rows has identity transport.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem torusVerticalFluxAssignment_right_transport_of_ne (p q : X) (b : Bool) (l : G)
    (h₀ : q.2 ≠ p.2) (h₁ : q.2 ≠ p.2 + 1) :
    regularDirectedTransport (torusVerticalFluxAssignment p b l)
      (torusGraph_adj_right q.1 q.2) = 1 := by
  have hn (y : ZMod height) (hy : q.2 ≠ y) :
      Edge.ofAdj (torusGraph_adj_right q.1 q.2) ≠
      Edge.ofAdj (torusGraph_adj_right p.1 y) :=
    Edge.ofAdj_ne_of_endpoint_coordinates (torusGraph_adj_right q.1 q.2)
      (torusGraph_adj_right p.1 y) Prod.snd rfl (Or.inl hy)
  simp [regularDirectedTransport, torusVerticalFluxAssignment, hn _ h₀, hn _ h₁]
/-- Seven native transports determine the internal ordered coefficients.
Source: SCP10, the elementary two-plaquette block, lines 2271–2305. -/
theorem verticalTwoPlaquette_internal_eq_of_transports (p : X) (u w : Edge Γₜ → G)
    (hL : regularDirectedTransport u (torusGraph_adj_up p.1 p.2) =
      regularDirectedTransport w (torusGraph_adj_up p.1 p.2))
    (hB : regularDirectedTransport u (torusGraph_adj_right p.1 p.2) =
      regularDirectedTransport w (torusGraph_adj_right p.1 p.2))
    (hU : regularDirectedTransport u (torusGraph_adj_up p.1 (p.2 + 1)) =
      regularDirectedTransport w (torusGraph_adj_up p.1 (p.2 + 1)))
    (hM : regularDirectedTransport u (torusGraph_adj_right p.1 (p.2 + 1)) =
      regularDirectedTransport w (torusGraph_adj_right p.1 (p.2 + 1)))
    (hT : regularDirectedTransport u (torusGraph_adj_right p.1 (p.2 + 2)) =
      regularDirectedTransport w (torusGraph_adj_right p.1 (p.2 + 2)))
    (hR : regularDirectedTransport u (torusGraph_adj_up (p.1 + 1) p.2) =
      regularDirectedTransport w (torusGraph_adj_up (p.1 + 1) p.2))
    (hV : regularDirectedTransport u (torusGraph_adj_up (p.1 + 1) (p.2 + 1)) =
      regularDirectedTransport w (torusGraph_adj_up (p.1 + 1) (p.2 + 1)))
    (e : Edge Γₜ) (he : e.1.1 ∈ verticalTwoPlaquetteRegion p ∧
      e.1.2 ∈ verticalTwoPlaquetteRegion p) : u e = w e := by
  let φ := verticalTwoPlaquetteIso p
  have hv (i : Fin 6) : (φ i).1 =
      (p.1 + ((![0, 0, 0, 1, 1, 1] i : ℕ) : ZMod width),
       p.2 + ((![0, 1, 2, 2, 1, 0] i : ℕ) : ZMod height)) := verticalTwoPlaquetteIso_apply p i
  refine twoPlaquette_internal_eq_of_edgeTransports (verticalTwoPlaquetteRegion p) φ u w
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ e he
  · have hi := hv 0
    have hj := hv 1
    norm_num at hi hj
    have hd (a : Edge Γₜ → G) :
        regularDirectedTransport a (SimpleGraph.induce_adj.mp (φ.map_rel_iff'.mpr
          (by decide : twoPlaquetteGraph.Adj 0 1))) =
        regularDirectedTransport a (torusGraph_adj_up p.1 p.2) :=
      regularDirectedTransport_eq_of_endpoints a _ (torusGraph_adj_up p.1 p.2)
        (by simpa [add_assoc, one_add_one_eq_two] using hi)
        (by simpa [add_assoc, one_add_one_eq_two] using hj)
    exact (hd u).trans (hL.trans (hd w).symm)
  · have hi := hv 0
    have hj := hv 5
    norm_num at hi hj
    have hd (a : Edge Γₜ → G) :
        regularDirectedTransport a (SimpleGraph.induce_adj.mp (φ.map_rel_iff'.mpr
          (by decide : twoPlaquetteGraph.Adj 0 5))) =
        regularDirectedTransport a (torusGraph_adj_right p.1 p.2) :=
      regularDirectedTransport_eq_of_endpoints a _ (torusGraph_adj_right p.1 p.2)
        (by simpa [add_assoc, one_add_one_eq_two] using hi)
        (by simpa [add_assoc, one_add_one_eq_two] using hj)
    exact (hd u).trans (hB.trans (hd w).symm)
  · have hi := hv 1
    have hj := hv 2
    norm_num at hi hj
    have hd (a : Edge Γₜ → G) :
        regularDirectedTransport a (SimpleGraph.induce_adj.mp (φ.map_rel_iff'.mpr
          (by decide : twoPlaquetteGraph.Adj 1 2))) =
        regularDirectedTransport a (torusGraph_adj_up p.1 (p.2 + 1)) :=
      regularDirectedTransport_eq_of_endpoints a _ (torusGraph_adj_up p.1 (p.2 + 1))
        (by simpa [add_assoc, one_add_one_eq_two] using hi)
        (by simpa [add_assoc, one_add_one_eq_two] using hj)
    exact (hd u).trans (hU.trans (hd w).symm)
  · have hi := hv 1
    have hj := hv 4
    norm_num at hi hj
    have hd (a : Edge Γₜ → G) :
        regularDirectedTransport a (SimpleGraph.induce_adj.mp (φ.map_rel_iff'.mpr
          (by decide : twoPlaquetteGraph.Adj 1 4))) =
        regularDirectedTransport a (torusGraph_adj_right p.1 (p.2 + 1)) :=
      regularDirectedTransport_eq_of_endpoints a _ (torusGraph_adj_right p.1 (p.2 + 1))
        (by simpa [add_assoc, one_add_one_eq_two] using hi)
        (by simpa [add_assoc, one_add_one_eq_two] using hj)
    exact (hd u).trans (hM.trans (hd w).symm)
  · have hi := hv 2
    have hj := hv 3
    norm_num at hi hj
    have hd (a : Edge Γₜ → G) :
        regularDirectedTransport a (SimpleGraph.induce_adj.mp (φ.map_rel_iff'.mpr
          (by decide : twoPlaquetteGraph.Adj 2 3))) =
        regularDirectedTransport a (torusGraph_adj_right p.1 (p.2 + 2)) :=
      regularDirectedTransport_eq_of_endpoints a _ (torusGraph_adj_right p.1 (p.2 + 2))
        (by simpa [add_assoc, one_add_one_eq_two] using hi)
        (by simpa [add_assoc, one_add_one_eq_two] using hj)
    exact (hd u).trans (hT.trans (hd w).symm)
  · have hi := hv 3
    have hj := hv 4
    norm_num at hi hj
    have hd (a : Edge Γₜ → G) :
        regularDirectedTransport a (SimpleGraph.induce_adj.mp (φ.map_rel_iff'.mpr
          (by decide : twoPlaquetteGraph.Adj 3 4))) =
        regularDirectedTransport a (torusGraph_adj_up (p.1 + 1) (p.2 + 1)).symm :=
      regularDirectedTransport_eq_of_endpoints a _ (torusGraph_adj_up (p.1 + 1) (p.2 + 1)).symm
        (by simpa [add_assoc, one_add_one_eq_two] using hi)
        (by simpa [add_assoc, one_add_one_eq_two] using hj)
    exact (hd u).trans ((regularDirectedTransport_symm u
        (torusGraph_adj_up (p.1 + 1) (p.2 + 1))).trans
      ((congrArg (fun x : G => x⁻¹) hV).trans
        ((regularDirectedTransport_symm w
          (torusGraph_adj_up (p.1 + 1) (p.2 + 1))).symm.trans (hd w).symm)))
  · have hi := hv 4
    have hj := hv 5
    norm_num at hi hj
    have hd (a : Edge Γₜ → G) :
        regularDirectedTransport a (SimpleGraph.induce_adj.mp (φ.map_rel_iff'.mpr
          (by decide : twoPlaquetteGraph.Adj 4 5))) =
        regularDirectedTransport a (torusGraph_adj_up (p.1 + 1) p.2).symm :=
      regularDirectedTransport_eq_of_endpoints a _ (torusGraph_adj_up (p.1 + 1) p.2).symm
        (by simpa [add_assoc, one_add_one_eq_two] using hi)
        (by simpa [add_assoc, one_add_one_eq_two] using hj)
    exact (hd u).trans ((regularDirectedTransport_symm u (torusGraph_adj_up (p.1 + 1) p.2)).trans
      ((congrArg (fun x : G => x⁻¹) hR).trans
        ((regularDirectedTransport_symm w
          (torusGraph_adj_up (p.1 + 1) p.2)).symm.trans (hd w).symm)))
end
section
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (3 < width)] [Fact (2 < height)]
local instance horizontalTableWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 3 < width); omega⟩
local instance horizontalTableHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
/-- Seven native transports determine the internal ordered coefficients.
Source: SCP10, the elementary two-plaquette block, lines 2271–2305. -/
theorem translatedTwoPlaquette_internal_eq_of_transports (p : X) (u w : Edge Γₜ → G)
    (hL : regularDirectedTransport u (torusGraph_adj_right p.1 p.2) =
      regularDirectedTransport w (torusGraph_adj_right p.1 p.2))
    (hB : regularDirectedTransport u (torusGraph_adj_up p.1 p.2) =
      regularDirectedTransport w (torusGraph_adj_up p.1 p.2))
    (hU : regularDirectedTransport u (torusGraph_adj_right (p.1 + 1) p.2) =
      regularDirectedTransport w (torusGraph_adj_right (p.1 + 1) p.2))
    (hM : regularDirectedTransport u (torusGraph_adj_up (p.1 + 1) p.2) =
      regularDirectedTransport w (torusGraph_adj_up (p.1 + 1) p.2))
    (hT : regularDirectedTransport u (torusGraph_adj_up (p.1 + 2) p.2) =
      regularDirectedTransport w (torusGraph_adj_up (p.1 + 2) p.2))
    (hR : regularDirectedTransport u (torusGraph_adj_right p.1 (p.2 + 1)) =
      regularDirectedTransport w (torusGraph_adj_right p.1 (p.2 + 1)))
    (hV : regularDirectedTransport u (torusGraph_adj_right (p.1 + 1) (p.2 + 1)) =
      regularDirectedTransport w (torusGraph_adj_right (p.1 + 1) (p.2 + 1)))
    (e : Edge Γₜ) (he : e.1.1 ∈ translatedTwoPlaquetteRegion p ∧
      e.1.2 ∈ translatedTwoPlaquetteRegion p) : u e = w e := by
  let φ := translatedTwoPlaquetteIso p
  have hv (i : Fin 6) : (φ i).1 =
      (p.1 + ((![0, 1, 2, 2, 1, 0] i : ℕ) : ZMod width),
       p.2 + ((![0, 0, 0, 1, 1, 1] i : ℕ) : ZMod height)) := by
    change (((![0, 1, 2, 2, 1, 0] i : ℕ) : ZMod width) + p.1,
      ((![0, 0, 0, 1, 1, 1] i : ℕ) : ZMod height) + p.2) = _
    simp only [add_comm]
  refine twoPlaquette_internal_eq_of_edgeTransports (translatedTwoPlaquetteRegion p) φ u w
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ e he
  · have hi := hv 0
    have hj := hv 1
    norm_num at hi hj
    have hd (a : Edge Γₜ → G) :
        regularDirectedTransport a (SimpleGraph.induce_adj.mp (φ.map_rel_iff'.mpr
          (by decide : twoPlaquetteGraph.Adj 0 1))) =
        regularDirectedTransport a (torusGraph_adj_right p.1 p.2) :=
      regularDirectedTransport_eq_of_endpoints a _ (torusGraph_adj_right p.1 p.2)
        (by simpa [add_assoc, one_add_one_eq_two] using hi)
        (by simpa [add_assoc, one_add_one_eq_two] using hj)
    exact (hd u).trans (hL.trans (hd w).symm)
  · have hi := hv 0
    have hj := hv 5
    norm_num at hi hj
    have hd (a : Edge Γₜ → G) :
        regularDirectedTransport a (SimpleGraph.induce_adj.mp (φ.map_rel_iff'.mpr
          (by decide : twoPlaquetteGraph.Adj 0 5))) =
        regularDirectedTransport a (torusGraph_adj_up p.1 p.2) :=
      regularDirectedTransport_eq_of_endpoints a _ (torusGraph_adj_up p.1 p.2)
        (by simpa [add_assoc, one_add_one_eq_two] using hi)
        (by simpa [add_assoc, one_add_one_eq_two] using hj)
    exact (hd u).trans (hB.trans (hd w).symm)
  · have hi := hv 1
    have hj := hv 2
    norm_num at hi hj
    have hd (a : Edge Γₜ → G) :
        regularDirectedTransport a (SimpleGraph.induce_adj.mp (φ.map_rel_iff'.mpr
          (by decide : twoPlaquetteGraph.Adj 1 2))) =
        regularDirectedTransport a (torusGraph_adj_right (p.1 + 1) p.2) :=
      regularDirectedTransport_eq_of_endpoints a _ (torusGraph_adj_right (p.1 + 1) p.2)
        (by simpa [add_assoc, one_add_one_eq_two] using hi)
        (by simpa [add_assoc, one_add_one_eq_two] using hj)
    exact (hd u).trans (hU.trans (hd w).symm)
  · have hi := hv 1
    have hj := hv 4
    norm_num at hi hj
    have hd (a : Edge Γₜ → G) :
        regularDirectedTransport a (SimpleGraph.induce_adj.mp (φ.map_rel_iff'.mpr
          (by decide : twoPlaquetteGraph.Adj 1 4))) =
        regularDirectedTransport a (torusGraph_adj_up (p.1 + 1) p.2) :=
      regularDirectedTransport_eq_of_endpoints a _ (torusGraph_adj_up (p.1 + 1) p.2)
        (by simpa [add_assoc, one_add_one_eq_two] using hi)
        (by simpa [add_assoc, one_add_one_eq_two] using hj)
    exact (hd u).trans (hM.trans (hd w).symm)
  · have hi := hv 2
    have hj := hv 3
    norm_num at hi hj
    have hd (a : Edge Γₜ → G) :
        regularDirectedTransport a (SimpleGraph.induce_adj.mp (φ.map_rel_iff'.mpr
          (by decide : twoPlaquetteGraph.Adj 2 3))) =
        regularDirectedTransport a (torusGraph_adj_up (p.1 + 2) p.2) :=
      regularDirectedTransport_eq_of_endpoints a _ (torusGraph_adj_up (p.1 + 2) p.2)
        (by simpa [add_assoc, one_add_one_eq_two] using hi)
        (by simpa [add_assoc, one_add_one_eq_two] using hj)
    exact (hd u).trans (hT.trans (hd w).symm)
  · have hi := hv 3
    have hj := hv 4
    norm_num at hi hj
    have hd (a : Edge Γₜ → G) :
        regularDirectedTransport a (SimpleGraph.induce_adj.mp (φ.map_rel_iff'.mpr
          (by decide : twoPlaquetteGraph.Adj 3 4))) =
        regularDirectedTransport a (torusGraph_adj_right (p.1 + 1) (p.2 + 1)).symm :=
      regularDirectedTransport_eq_of_endpoints a _ (torusGraph_adj_right (p.1 + 1) (p.2 + 1)).symm
        (by simpa [add_assoc, one_add_one_eq_two] using hi)
        (by simpa [add_assoc, one_add_one_eq_two] using hj)
    exact (hd u).trans ((regularDirectedTransport_symm u
        (torusGraph_adj_right (p.1 + 1) (p.2 + 1))).trans
      ((congrArg (fun x : G => x⁻¹) hV).trans
        ((regularDirectedTransport_symm w
          (torusGraph_adj_right (p.1 + 1) (p.2 + 1))).symm.trans (hd w).symm)))
  · have hi := hv 4
    have hj := hv 5
    norm_num at hi hj
    have hd (a : Edge Γₜ → G) :
        regularDirectedTransport a (SimpleGraph.induce_adj.mp (φ.map_rel_iff'.mpr
          (by decide : twoPlaquetteGraph.Adj 4 5))) =
        regularDirectedTransport a (torusGraph_adj_right p.1 (p.2 + 1)).symm :=
      regularDirectedTransport_eq_of_endpoints a _ (torusGraph_adj_right p.1 (p.2 + 1)).symm
        (by simpa [add_assoc, one_add_one_eq_two] using hi)
        (by simpa [add_assoc, one_add_one_eq_two] using hj)
    exact (hd u).trans ((regularDirectedTransport_symm u (torusGraph_adj_right p.1 (p.2 + 1))).trans
      ((congrArg (fun x : G => x⁻¹) hR).trans
        ((regularDirectedTransport_symm w
          (torusGraph_adj_right p.1 (p.2 + 1))).symm.trans (hd w).symm)))
end
end TNLean.PEPS

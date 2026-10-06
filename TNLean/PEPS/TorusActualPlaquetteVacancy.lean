/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularTreeGaugeTransport
import TNLean.PEPS.RegularInternalGaugeTransport
import TNLean.PEPS.TranslatedTwoPlaquetteGeometry
import TNLean.PEPS.TorusPlaquetteFluxMeasurement

/-!
# Actual vacancy of the neighbouring native plaquette

The original bond operators determine their normalized tree gauge. For the
right plaquette in the actual horizontal two-plaquette block, vacancy is
precisely agreement of the middle upward transport with that gauge gradient.
The three other sides are edges of the derived spanning tree.

Source: SCP10, arXiv:1001.3807, Theorem 6.16, lines 2271–2305, using the
coordinate construction, lines 1765–1920.

**Scope restriction (finite torus):** Width is at least four and height at least
three; periodic seams are included. This is an auxiliary vacancy criterion,
not the complete prescribed braid. See
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (3 < width)] [Fact (2 < height)]
local instance vacancyWidthTwo : Fact (2 < width) :=
  ⟨by have := Fact.out (p := 3 < width); omega⟩
local instance vacancyWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 3 < width); omega⟩
local instance vacancyHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
variable {G : Type*} [Group G] [Fintype G]

/-- The actual translated numbering has the six cyclic coordinates of the
outer spanning path. Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem translatedTwoPlaquetteIso_vertex_coordinates (p : X) (i : Fin 6) :
    (translatedTwoPlaquetteIso p i).1 =
      (p.1 + ((![0,1,2,2,1,0] i : ℕ) : ZMod width),
        p.2 + ((![0,0,0,1,1,1] i : ℕ) : ZMod height)) := by
  change (((![0,1,2,2,1,0] i : ℕ) : ZMod width) + p.1,
    ((![0,0,0,1,1,1] i : ℕ) : ZMod height) + p.2) = _
  simp only [add_comm]

/-- The actual neighbouring plaquette is vacant exactly when its non-tree
transport equals the tree gauge gradient. Source: SCP10, Theorem 6.16,
lines 2271–2305. -/
theorem regularWalkHolonomy_rightPlaquette_eq_one_iff_treeGauge
    (p : X) (u : Edge Γₜ → G) :
    regularWalkHolonomy u (torusPlaquetteWalk (p.1 + 1, p.2)) = 1 ↔
    regularDirectedTransport u (torusGraph_adj_up (p.1 + 1) p.2) =
      (regularRegionTreeGauge (translatedTwoPlaquetteRegion p)
        (translatedTwoPlaquetteTree p) (translatedTwoPlaquetteTree_le p)
        (translatedTwoPlaquetteTree_isTree p) (translatedTwoPlaquetteIso p 0) u).1
        (translatedTwoPlaquetteIso p 4) *
      ((regularRegionTreeGauge (translatedTwoPlaquetteRegion p)
        (translatedTwoPlaquetteTree p) (translatedTwoPlaquetteTree_le p)
        (translatedTwoPlaquetteTree_isTree p) (translatedTwoPlaquetteIso p 0) u).1
        (translatedTwoPlaquetteIso p 1))⁻¹ := by
  let φ := translatedTwoPlaquetteIso p
  have htree {i j : Fin 6} (h : twoPlaquetteTree.Adj i j) :
      (translatedTwoPlaquetteTree p).Adj (φ i) (φ j) := by
    change twoPlaquetteTree.Adj
      ((translatedTwoPlaquetteVertexEquiv p).symm (translatedTwoPlaquetteVertexEquiv p i))
      ((translatedTwoPlaquetteVertexEquiv p).symm (translatedTwoPlaquetteVertexEquiv p j))
    simpa only [Equiv.symm_apply_apply] using h
  have h₁₂ := htree (by decide : twoPlaquetteTree.Adj 1 2)
  have h₂₃ := htree (by decide : twoPlaquetteTree.Adj 2 3)
  have h₃₄ := htree (by decide : twoPlaquetteTree.Adj 3 4)
  have h₁₄ : (Γₜ).Adj (φ 1).1 (φ 4).1 :=
    SimpleGraph.induce_adj.mp (φ.map_rel_iff'.mpr (by decide : twoPlaquetteGraph.Adj 1 4))
  have hv₁ : (φ 1).1 = (p.1 + 1, p.2) := by
    simpa using translatedTwoPlaquetteIso_vertex_coordinates p 1
  have hv₂ : (φ 2).1 = (p.1 + 1 + 1, p.2) := by
    have H := translatedTwoPlaquetteIso_vertex_coordinates p 2
    norm_num at H
    convert H using 1; simp only [add_assoc, one_add_one_eq_two]
  have hv₃ : (φ 3).1 = (p.1 + 1 + 1, p.2 + 1) := by
    have H := translatedTwoPlaquetteIso_vertex_coordinates p 3
    norm_num at H
    convert H using 1; simp only [add_assoc, one_add_one_eq_two]
  have hv₄ : (φ 4).1 = (p.1 + 1, p.2 + 1) := by
    simpa using translatedTwoPlaquetteIso_vertex_coordinates p 4
  have hd₁₂ := regularDirectedTransport_eq_of_endpoints u
    (SimpleGraph.induce_adj.mp (translatedTwoPlaquetteTree_le p h₁₂))
    (torusGraph_adj_right (p.1 + 1) p.2) hv₁ hv₂
  have hd₂₃ := regularDirectedTransport_eq_of_endpoints u
    (SimpleGraph.induce_adj.mp (translatedTwoPlaquetteTree_le p h₂₃))
    (torusGraph_adj_up (p.1 + 1 + 1) p.2) hv₂ hv₃
  have hd₃₄ := regularDirectedTransport_eq_of_endpoints u
    (SimpleGraph.induce_adj.mp (translatedTwoPlaquetteTree_le p h₃₄))
    (torusGraph_adj_right (p.1 + 1) (p.2 + 1)).symm hv₃ hv₄
  have hd₁₄ := regularDirectedTransport_eq_of_endpoints u h₁₄
    (torusGraph_adj_up (p.1 + 1) p.2) hv₁ hv₄
  have H := regularRegionTreeGauge_fourStep_holonomy_eq_one_iff
    (translatedTwoPlaquetteRegion p) (translatedTwoPlaquetteTree p)
    (translatedTwoPlaquetteTree_le p) (translatedTwoPlaquetteTree_isTree p)
    (φ 0) u (φ 1) (φ 2) (φ 3) (φ 4) h₁₂ h₂₃ h₃₄ h₁₄
  simp only [regularWalkHolonomy_cons, regularWalkHolonomy_nil, one_mul,
    regularDirectedTransport_symm u h₁₄] at H
  rw [hd₁₂, hd₂₃, hd₃₄, hd₁₄,
    regularDirectedTransport_symm u (torusGraph_adj_right (p.1 + 1) (p.2 + 1))] at H
  rw [regularWalkHolonomy_torusPlaquetteWalk]
  exact H

/-- Actual plaquette vacancy is exactly triviality of its derived native cycle
residual, with no supplied background gauge. Source: SCP10, Theorem 6.16,
lines 2271–2305. -/
theorem regularRegionTreeCycleResidual_middle_eq_one_iff_rightPlaquette
    (p : X) (u : Edge Γₜ → G) :
    regularRegionTreeCycleResidual (translatedTwoPlaquetteRegion p)
      (translatedTwoPlaquetteTree p) (translatedTwoPlaquetteTree_le p)
      (translatedTwoPlaquetteTree_isTree p) (translatedTwoPlaquetteIso p 0) u
      (translatedTwoPlaquetteCycleBond p 1) = 1 ↔
    regularWalkHolonomy u (torusPlaquetteWalk (p.1 + 1, p.2)) = 1 := by
  let φ := translatedTwoPlaquetteIso p
  have hv₁ : (φ 1).1 = (p.1 + 1, p.2) := by
    simpa using translatedTwoPlaquetteIso_vertex_coordinates p 1
  have hv₄ : (φ 4).1 = (p.1 + 1, p.2 + 1) := by
    simpa using translatedTwoPlaquetteIso_vertex_coordinates p 4
  have ha : (Γₜ).Adj (φ 1).1 (φ 4).1 :=
    SimpleGraph.induce_adj.mp (φ.map_rel_iff'.mpr (by decide : twoPlaquetteGraph.Adj 1 4))
  have he : Edge.ofAdj ha = (translatedTwoPlaquetteCycleBond p 1).1.1 := by
    rw [translatedTwoPlaquetteCycleBond_eq_up]
    simpa only [Fin.val_one, Nat.cast_one] using
      Edge.ofAdj_eq_ofAdj ha (torusGraph_adj_up (p.1 + 1) p.2) (Or.inl ⟨hv₁, hv₄⟩)
  have H := regularRegionGaugeResidual_eq_one_iff_directedTransport
    (translatedTwoPlaquetteRegion p) (translatedTwoPlaquetteTree p)
    (translatedTwoPlaquetteTree_le p) (translatedTwoPlaquetteTree_isTree p)
    (φ 0) u ha (φ 1).2 (φ 4).2
  have hs : (⟨Edge.ofAdj ha, by
      rw [he]
      exact (translatedTwoPlaquetteCycleBond p 1).1.2⟩ : {e : Edge Γₜ //
      e.1.1 ∈ translatedTwoPlaquetteRegion p ∧ e.1.2 ∈ translatedTwoPlaquetteRegion p}) =
      (translatedTwoPlaquetteCycleBond p 1).1 := Subtype.ext he
  rw [hs, regularDirectedTransport_eq_of_endpoints u ha
    (torusGraph_adj_up (p.1 + 1) p.2) hv₁ hv₄] at H
  exact H.trans (regularWalkHolonomy_rightPlaquette_eq_one_iff_treeGauge p u).symm

end TNLean.PEPS

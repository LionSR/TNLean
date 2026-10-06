/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.EdgeMapSubgraph
import TNLean.PEPS.TwoPlaquetteGeometry
import TNLean.PEPS.TorusTranslation
import TNLean.PEPS.RegionTransport
import TNLean.PEPS.TorusWindowComplement

/-!
# The actual two-plaquette block at every torus position

Translation preserves the torus graph, including bonds crossing periodic seams.
The translated six-site numbering therefore identifies its induced graph with
the same two-plaquette graph. The fixed spanning path and two remaining vertical
bonds are constructed in the actual induced region. The selected vertical bonds
are described as native upward steps; their ordered endpoints may reverse at
the vertical seam.

Source: SCP10, arXiv:1001.3807, Theorem 6.16, local source lines 2271–2305.

**Scope restriction (finite-torus two-plaquette geometry):** The horizontal
period is at least four and the vertical period at least three. Every starting
position is allowed, including either periodic seam. The unrestricted lattice
statement remains separate; see
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (3 < width)] [Fact (2 < height)]
local instance translatedTwoPlaquetteWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 3 < width); omega⟩
local instance translatedTwoPlaquetteHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height

/-- The six-site numbering translated to the given torus position.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
def translatedTwoPlaquetteVertex (v : X) (i : Fin 6) : X :=
  translate v.1 v.2 (twoPlaquetteTorusVertex i)

/-- The literal set of the six translated physical sites.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
def translatedTwoPlaquetteRegion (v : X) : Finset X :=
  Finset.univ.image (translatedTwoPlaquetteVertex v)

private theorem vertex_injective (v : X) :
    Function.Injective (translatedTwoPlaquetteVertex v) :=
  (translate v.1 v.2).injective.comp twoPlaquetteTorusVertex_injective

/-- The derived numbering of the actual translated region.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
noncomputable def translatedTwoPlaquetteVertexEquiv (v : X) :
    Fin 6 ≃ {x : X // x ∈ translatedTwoPlaquetteRegion v} :=
  Equiv.ofBijective (fun i => ⟨translatedTwoPlaquetteVertex v i,
    Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩) (by
    constructor
    · intro i j h
      exact vertex_injective v (congrArg Subtype.val h)
    · intro x
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp x.2
      exact ⟨i, Subtype.ext hi⟩)

/-- The two-plaquette graph is the actual induced graph at every position.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
noncomputable def translatedTwoPlaquetteIso (v : X) :
    twoPlaquetteGraph ≃g (Γₜ).induce (translatedTwoPlaquetteRegion v : Set X) where
  __ := translatedTwoPlaquetteVertexEquiv v
  map_rel_iff' := by
    intro i j
    change (Γₜ).Adj (translate v.1 v.2 (twoPlaquetteTorusVertex i))
      (translate v.1 v.2 (twoPlaquetteTorusVertex j)) ↔ _
    exact (translate v.1 v.2).map_rel_iff'.trans (twoPlaquetteTorusVertex_adj_iff i j)

/-- The fixed spanning path in the actual translated region.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
noncomputable def translatedTwoPlaquetteTree (v : X) :
    SimpleGraph {x : X // x ∈ translatedTwoPlaquetteRegion v} :=
  twoPlaquetteTree.comap (translatedTwoPlaquetteVertexEquiv v).symm

noncomputable instance (v : X) : DecidableRel (translatedTwoPlaquetteTree v).Adj := by
  unfold translatedTwoPlaquetteTree
  infer_instance

/-- The translated spanning path is a tree.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem translatedTwoPlaquetteTree_isTree (v : X) :
    (translatedTwoPlaquetteTree v).IsTree :=
  (SimpleGraph.Iso.isTree_iff (SimpleGraph.Iso.comap
    (translatedTwoPlaquetteVertexEquiv v).symm twoPlaquetteTree)).mpr
      twoPlaquetteTree_isTree

/-- The translated tree lies in the actual induced torus graph.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem translatedTwoPlaquetteTree_le (v : X) :
    translatedTwoPlaquetteTree v ≤ (Γₜ).induce (translatedTwoPlaquetteRegion v : Set X) := by
  intro x y h
  have ht := twoPlaquetteTree_le h
  have ha := (translatedTwoPlaquetteIso v).map_rel_iff'.mpr ht
  change (Γₜ).Adj
    ((translatedTwoPlaquetteVertexEquiv v) ((translatedTwoPlaquetteVertexEquiv v).symm x)).1
    ((translatedTwoPlaquetteVertexEquiv v) ((translatedTwoPlaquetteVertexEquiv v).symm y)).1 at ha
  change (Γₜ).Adj x.1 y.1
  simpa only [Equiv.apply_symm_apply] using ha

/-- The translated block contains exactly six physical spins.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem translatedTwoPlaquetteRegion_card (v : X) :
    (translatedTwoPlaquetteRegion v).card = 6 := by
  rw [← Fintype.card_coe, ← Fintype.card_congr (translatedTwoPlaquetteVertexEquiv v)]
  rfl

/-- The six-site set is the image of the origin region under torus translation.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem translatedTwoPlaquetteRegion_eq_map (v : X) :
    translatedTwoPlaquetteRegion v = Region.map (translate v.1 v.2)
      (twoPlaquetteTorusRegion (width := width) (height := height)) := by
  simp only [translatedTwoPlaquetteRegion,
    twoPlaquetteTorusRegion, Region.map, Finset.map_eq_image, Finset.image_image,
    Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv]
  rfl

/-- The actual region is the cyclic rectangle of width three and height two.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem translatedTwoPlaquetteRegion_eq_arcRectangle (v : X) :
    translatedTwoPlaquetteRegion v = torusArcRectangle v 3 2 := by
  rw [translatedTwoPlaquetteRegion_eq_map, twoPlaquetteTorusRegion_eq_rectangle]
  ext w
  rw [mem_Region_map, mem_torusContiguousRectangle, mem_torusArcRectangle]
  change (0 ≤ (w.1 - v.1).val ∧ (w.1 - v.1).val < 0 + 3 ∧
    0 ≤ (w.2 - v.2).val ∧ (w.2 - v.2).val < 0 + 2) ↔ _
  simp

/-- The actual translated induced region is connected.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem translatedTwoPlaquetteRegion_connected (v : X) :
    ((Γₜ).induce (translatedTwoPlaquetteRegion v : Set X)).Connected :=
  (translatedTwoPlaquetteTree_isTree v).connected.mono (translatedTwoPlaquetteTree_le v)

/-- The actual translated region has seven internal bonds.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem translatedTwoPlaquetteRegion_card_internalEdges (v : X) :
    Fintype.card {e : Edge Γₜ // e.1.1 ∈ translatedTwoPlaquetteRegion v ∧
      e.1.2 ∈ translatedTwoPlaquetteRegion v} = 7 := by
  rw [← Fintype.card_congr (inducedRegionEdgeEquiv (translatedTwoPlaquetteRegion v)),
    ← Fintype.card_congr (Edge.equiv (translatedTwoPlaquetteIso v))]
  exact twoPlaquetteGraph_card_edges

/-- The two derived non-tree vertical bonds of the translated region.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
noncomputable def translatedTwoPlaquetteCycleBond (v : X) (i : Fin 2) :
    {e : {e : Edge Γₜ // e.1.1 ∈ translatedTwoPlaquetteRegion v ∧
      e.1.2 ∈ translatedTwoPlaquetteRegion v} //
      ¬ (translatedTwoPlaquetteTree v).Adj ⟨e.1.1.1, e.2.1⟩ ⟨e.1.1.2, e.2.2⟩} := by
  let e := Edge.equiv (translatedTwoPlaquetteIso v) (twoPlaquetteCycleBond i)
  refine ⟨inducedRegionEdgeEquiv (translatedTwoPlaquetteRegion v) e, ?_⟩
  change ¬ (translatedTwoPlaquetteTree v).Adj e.1.1 e.1.2
  exact (Edge.comap_adj_map_iff (translatedTwoPlaquetteIso v)
    twoPlaquetteTree (twoPlaquetteCycleBond i)).not.mpr (twoPlaquetteCycleBond_not_tree i)

/-- The two translated non-tree bonds are distinct.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem translatedTwoPlaquetteCycleBond_injective (v : X) :
    Function.Injective (translatedTwoPlaquetteCycleBond v) := by
  intro i j h
  apply twoPlaquetteCycleBond_injective
  apply (Edge.equiv (translatedTwoPlaquetteIso v)).injective
  apply (inducedRegionEdgeEquiv (translatedTwoPlaquetteRegion v)).injective
  exact congrArg Subtype.val h

/-- Each selected bond is the actual upward native step, with sorting retained.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem translatedTwoPlaquetteCycleBond_eq_up (v : X) (i : Fin 2) :
    (translatedTwoPlaquetteCycleBond v i).1.1 =
      Edge.ofAdj (torusGraph_adj_up (v.1 + (i.val : ZMod width)) v.2) := by
  symm
  apply Edge.ofAdj_eq_of_endpoints
  have he := Edge.map_endpoints (translatedTwoPlaquetteIso v) (twoPlaquetteCycleBond i)
  have hlo : (translatedTwoPlaquetteIso v (twoPlaquetteCycleBond i).1.1).1 =
      (v.1 + (i.val : ZMod width), v.2) := by
    fin_cases i
    · change (((0 : ℕ) : ZMod width) + v.1, ((0 : ℕ) : ZMod height) + v.2) =
        (v.1 + ((0 : ℕ) : ZMod width), v.2)
      simp
    · change (((1 : ℕ) : ZMod width) + v.1, ((0 : ℕ) : ZMod height) + v.2) =
        (v.1 + ((1 : ℕ) : ZMod width), v.2)
      simp [add_comm]
  have hhi : (translatedTwoPlaquetteIso v (twoPlaquetteCycleBond i).1.2).1 =
      (v.1 + (i.val : ZMod width), v.2 + 1) := by
    fin_cases i
    · change (((0 : ℕ) : ZMod width) + v.1, ((1 : ℕ) : ZMod height) + v.2) =
        (v.1 + ((0 : ℕ) : ZMod width), v.2 + 1)
      simp [add_comm]
    · change (((1 : ℕ) : ZMod width) + v.1, ((1 : ℕ) : ZMod height) + v.2) =
        (v.1 + ((1 : ℕ) : ZMod width), v.2 + 1)
      simp [add_comm]
  rcases he with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · exact Or.inl ⟨by simpa only [translatedTwoPlaquetteCycleBond, inducedRegionEdgeEquiv,
        Edge.equiv_apply, Equiv.coe_fn_mk, ← hlo] using (congrArg Subtype.val h₁).symm,
      by simpa only [translatedTwoPlaquetteCycleBond, inducedRegionEdgeEquiv,
        Edge.equiv_apply, Equiv.coe_fn_mk, ← hhi] using (congrArg Subtype.val h₂).symm⟩
  · exact Or.inr ⟨by simpa only [translatedTwoPlaquetteCycleBond, inducedRegionEdgeEquiv,
        Edge.equiv_apply, Equiv.coe_fn_mk, ← hlo] using (congrArg Subtype.val h₂).symm,
      by simpa only [translatedTwoPlaquetteCycleBond, inducedRegionEdgeEquiv,
        Edge.equiv_apply, Equiv.coe_fn_mk, ← hhi] using (congrArg Subtype.val h₁).symm⟩
end TNLean.PEPS

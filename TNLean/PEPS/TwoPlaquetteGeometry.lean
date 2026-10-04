/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.EdgeMapSubgraph
import TNLean.PEPS.TorusRectangleRegion
import TNLean.PEPS.RegularRegionCycleRank
import TNLean.PEPS.IsoTransport
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# The six-site geometry of two adjacent plaquettes

The sites are numbered along the path
(0,0), (1,0), (2,0), (2,1), (1,1), (0,1). The two-plaquette graph adds
its leftmost and middle vertical bonds to this path. Thus the fixed tree has
five edges and the induced graph has seven. The two remaining edges give
explicit distinct non-tree bond coordinates.

The native torus realization is the actual induced 3 by 2 rectangle at the
origin. Its coordinate change preserves adjacency, its internal edges, and
its spanning tree. The two non-tree bonds are oriented upward from (0,0)
to (0,1) and from (1,0) to (1,1).

Source: SCP10, the proof of moving fluxons, lines 2271–2305.

**Scope restriction (six-site torus geometry):** The native realization has
horizontal period at least four and vertical period at least three. A horizontal
period of three would add two wraparound edges inside this rectangle. These
are auxiliary graph statements for the finite local construction, rather than
the full flux-moving theorem; see
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

namespace TNLean.PEPS

/-- The graph of two adjacent squares, numbered along their outer five-edge path. -/
def twoPlaquetteGraph : SimpleGraph (Fin 6) :=
  SimpleGraph.pathGraph 6 ⊔
    SimpleGraph.fromEdgeSet {s(0, 5), s(1, 4)}

/-- The fixed spanning path through the six sites of two adjacent plaquettes. -/
def twoPlaquetteTree : SimpleGraph (Fin 6) := SimpleGraph.pathGraph 6

local instance twoPlaquettePathDecidableAdj : DecidableRel (SimpleGraph.pathGraph 6).Adj :=
  fun i j => decidable_of_iff (i.val + 1 = j.val ∨ j.val + 1 = i.val)
    SimpleGraph.pathGraph_adj.symm

instance : DecidableRel twoPlaquetteGraph.Adj := by
  unfold twoPlaquetteGraph
  infer_instance
instance : DecidableRel twoPlaquetteTree.Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.pathGraph 6).Adj)

/-- The fixed path is a subgraph of the two-plaquette graph. Source: SCP10, lines 2271–2305. -/
theorem twoPlaquetteTree_le : twoPlaquetteTree ≤ twoPlaquetteGraph := le_sup_left

/-- The five-edge spanning path is a tree. Source: SCP10, lines 2271–2305. -/
theorem twoPlaquetteTree_isTree : twoPlaquetteTree.IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨SimpleGraph.pathGraph_connected 5, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  decide

/-- The two adjacent squares form a connected graph. Source: SCP10, lines 2271–2305. -/
theorem twoPlaquetteGraph_connected : twoPlaquetteGraph.Connected :=
  twoPlaquetteTree_isTree.connected.mono twoPlaquetteTree_le

/-- Two adjacent plaquettes have seven internal bonds. Source: SCP10, lines 2271–2305. -/
theorem twoPlaquetteGraph_card_edges : Fintype.card (Edge twoPlaquetteGraph) = 7 := by
  rw [Fintype.card_congr (orderedEdgeEquivEdgeSet (Γ := twoPlaquetteGraph))]
  decide

/-- The fixed spanning path has five bonds. Source: SCP10, lines 2271–2305. -/
theorem twoPlaquetteTree_card_edges : Fintype.card (Edge twoPlaquetteTree) = 5 := by
  rw [Fintype.card_congr (orderedEdgeEquivEdgeSet (Γ := twoPlaquetteTree))]
  decide

/-- The leftmost and middle vertical bonds, in that order. -/
def twoPlaquetteCycleBond (i : Fin 2) : Edge twoPlaquetteGraph :=
  if i = 0 then ⟨(0, 5), by decide, by simp [twoPlaquetteGraph]⟩
  else ⟨(1, 4), by decide, by simp [twoPlaquetteGraph]⟩

/-- The two selected vertical bonds lie outside the spanning tree. Source: SCP10, lines
2271–2305. -/
theorem twoPlaquetteCycleBond_not_tree (i : Fin 2) :
    ¬ twoPlaquetteTree.Adj (twoPlaquetteCycleBond i).1.1
      (twoPlaquetteCycleBond i).1.2 := by
  fin_cases i <;> decide

/-- The selected vertical bonds are distinct. Source: SCP10, lines 2271–2305. -/
theorem twoPlaquetteCycleBond_injective : Function.Injective twoPlaquetteCycleBond := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [twoPlaquetteCycleBond]

/-- Every bond outside the spanning tree is one of the two selected vertical bonds. Source:
SCP10, lines 2271–2305. -/
theorem twoPlaquetteCycleBond_surjective_non_tree (e : Edge twoPlaquetteGraph)
    (he : ¬ twoPlaquetteTree.Adj e.1.1 e.1.2) :
    ∃ i, twoPlaquetteCycleBond i = e := by
  exact (by decide : ∀ e : Edge twoPlaquetteGraph,
    ¬ twoPlaquetteTree.Adj e.1.1 e.1.2 → ∃ i, twoPlaquetteCycleBond i = e) e he

private def twoPlaquetteX : Fin 6 → ℕ := ![0, 1, 2, 2, 1, 0]
private def twoPlaquetteY : Fin 6 → ℕ := ![0, 0, 0, 1, 1, 1]

/-- The six numbered sites as actual native torus vertices. -/
def twoPlaquetteTorusVertex {width height : ℕ} (i : Fin 6) : TorusVertex width height :=
  (twoPlaquetteX i, twoPlaquetteY i)

private theorem small_natCast_eq_iff {n a b : ℕ} (ha : a < n) (hb : b < n) :
    (a : ZMod n) = (b : ZMod n) ↔ a = b := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (3 < width)] [Fact (2 < height)]
local instance twoPlaquetteWidthFact : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 3 < width); omega⟩
local instance twoPlaquetteHeightFact : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 2 < height); omega⟩

omit [NeZero width] in
private theorem twoPlaquetteX_lt (i : Fin 6) : twoPlaquetteX i + 1 < width := by
  have hw := Fact.out (p := 3 < width)
  have hx : twoPlaquetteX i ≤ 2 := (by decide : ∀ j, twoPlaquetteX j ≤ 2) i
  omega
omit [NeZero height] in
private theorem twoPlaquetteY_lt (i : Fin 6) : twoPlaquetteY i + 1 < height := by
  have hh := Fact.out (p := 2 < height)
  have hy : twoPlaquetteY i ≤ 1 := (by decide : ∀ j, twoPlaquetteY j ≤ 1) i
  omega

omit [NeZero width] [NeZero height] in
/-- The six native torus sites are distinct at the stated periods. Source: SCP10, lines
2271–2305. -/
theorem twoPlaquetteTorusVertex_injective :
    Function.Injective (twoPlaquetteTorusVertex (width := width) (height := height)) := by
  intro i j hij
  have hx := congrArg Prod.fst hij
  have hy := congrArg Prod.snd hij
  change (twoPlaquetteX i : ZMod width) = (twoPlaquetteX j : ZMod width) at hx
  change (twoPlaquetteY i : ZMod height) = (twoPlaquetteY j : ZMod height) at hy
  have hx' := (small_natCast_eq_iff (by have := twoPlaquetteX_lt (width := width) i; omega)
    (by have := twoPlaquetteX_lt (width := width) j; omega)).mp hx
  have hy' := (small_natCast_eq_iff (by have := twoPlaquetteY_lt (height := height) i; omega)
    (by have := twoPlaquetteY_lt (height := height) j; omega)).mp hy
  exact (by decide : Function.Injective (fun k => (twoPlaquetteX k, twoPlaquetteY k)))
    (Prod.ext hx' hy')

/-- The fixed coordinate placement preserves and reflects native torus adjacency. Source: SCP10,
lines 2271–2305. -/
theorem twoPlaquetteTorusVertex_adj_iff (i j : Fin 6) :
    (torusGraph width height).Adj
      (twoPlaquetteTorusVertex i) (twoPlaquetteTorusVertex j) ↔
      twoPlaquetteGraph.Adj i j := by
  have hx (i : Fin 6) : twoPlaquetteX i < width := by
    have := twoPlaquetteX_lt (width := width) i; omega
  have hy (i : Fin 6) : twoPlaquetteY i < height := by
    have := twoPlaquetteY_lt (height := height) i; omega
  change ((twoPlaquetteY i : ZMod height) = (twoPlaquetteY j : ZMod height) ∧
    ((twoPlaquetteX i : ZMod width) + 1 = (twoPlaquetteX j : ZMod width) ∨
      (twoPlaquetteX j : ZMod width) + 1 = (twoPlaquetteX i : ZMod width))) ∨
    ((twoPlaquetteX i : ZMod width) = (twoPlaquetteX j : ZMod width) ∧
    ((twoPlaquetteY i : ZMod height) + 1 = (twoPlaquetteY j : ZMod height) ∨
      (twoPlaquetteY j : ZMod height) + 1 = (twoPlaquetteY i : ZMod height))) ↔ _
  rw [show (twoPlaquetteX i : ZMod width) + 1 = (↑(twoPlaquetteX i + 1)) by simp,
    show (twoPlaquetteX j : ZMod width) + 1 = (↑(twoPlaquetteX j + 1)) by simp,
    show (twoPlaquetteY i : ZMod height) + 1 = (↑(twoPlaquetteY i + 1)) by simp,
    show (twoPlaquetteY j : ZMod height) + 1 = (↑(twoPlaquetteY j + 1)) by simp]
  rw [small_natCast_eq_iff (hy i) (hy j),
    small_natCast_eq_iff (twoPlaquetteX_lt i) (hx j),
    small_natCast_eq_iff (twoPlaquetteX_lt j) (hx i),
    small_natCast_eq_iff (hx i) (hx j),
    small_natCast_eq_iff (twoPlaquetteY_lt i) (hy j),
    small_natCast_eq_iff (twoPlaquetteY_lt j) (hy i)]
  exact (by decide : ∀ a b : Fin 6,
    (twoPlaquetteY a = twoPlaquetteY b ∧
      (twoPlaquetteX a + 1 = twoPlaquetteX b ∨ twoPlaquetteX b + 1 = twoPlaquetteX a)) ∨
    (twoPlaquetteX a = twoPlaquetteX b ∧
      (twoPlaquetteY a + 1 = twoPlaquetteY b ∨ twoPlaquetteY b + 1 = twoPlaquetteY a)) ↔
    twoPlaquetteGraph.Adj a b) i j


/-- The actual set of six native sites of the two-plaquette block. -/
def twoPlaquetteTorusRegion : Finset (TorusVertex width height) :=
  Finset.univ.image twoPlaquetteTorusVertex

/-- The fixed numbering of the six native sites. -/
noncomputable def twoPlaquetteTorusVertexEquiv :
    Fin 6 ≃ {v : TorusVertex width height // v ∈ twoPlaquetteTorusRegion} :=
  Equiv.ofBijective (fun i => ⟨twoPlaquetteTorusVertex i,
    Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩) (by
    constructor
    · intro i j h
      exact twoPlaquetteTorusVertex_injective (congrArg Subtype.val h)
    · intro v
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp v.2
      exact ⟨i, Subtype.ext hi⟩)

/-- The two-plaquette graph is the actual graph induced on its six torus sites. -/
noncomputable def twoPlaquetteTorusIso :
    twoPlaquetteGraph ≃g (torusGraph width height).induce
      (twoPlaquetteTorusRegion (width := width) (height := height) :
      Set (TorusVertex width height)) where
  __ := twoPlaquetteTorusVertexEquiv
  map_rel_iff' := twoPlaquetteTorusVertex_adj_iff _ _

/-- The fixed spanning path, transported to the actual induced torus region. -/
noncomputable def twoPlaquetteTorusTree :
    SimpleGraph {v : TorusVertex width height // v ∈ twoPlaquetteTorusRegion} :=
  twoPlaquetteTree.comap twoPlaquetteTorusVertexEquiv.symm

noncomputable instance : DecidableRel (twoPlaquetteTorusTree (width := width)
    (height := height)).Adj := by
  unfold twoPlaquetteTorusTree
  infer_instance

omit [NeZero width] [NeZero height] in
/-- The transported path is an actual spanning tree of the native six-site region. Source:
SCP10, lines 2271–2305. -/
theorem twoPlaquetteTorusTree_isTree :
    (twoPlaquetteTorusTree (width := width) (height := height)).IsTree :=
  (SimpleGraph.Iso.isTree_iff (SimpleGraph.Iso.comap
    twoPlaquetteTorusVertexEquiv.symm twoPlaquetteTree)).mpr twoPlaquetteTree_isTree

/-- The transported path lies in the actual induced torus graph. Source: SCP10, lines 2271–2305. -/
theorem twoPlaquetteTorusTree_le :
    twoPlaquetteTorusTree ≤ (torusGraph width height).induce
      (twoPlaquetteTorusRegion (width := width) (height := height) :
        Set (TorusVertex width height)) := by
  intro u v h
  have ht := twoPlaquetteTree_le h
  have ha := (twoPlaquetteTorusIso (width := width) (height := height)).map_rel_iff'.mpr ht
  change (torusGraph width height).Adj
    (twoPlaquetteTorusVertexEquiv (twoPlaquetteTorusVertexEquiv.symm u)).1
    (twoPlaquetteTorusVertexEquiv (twoPlaquetteTorusVertexEquiv.symm v)).1 at ha
  change (torusGraph width height).Adj u.1 v.1
  simpa only [Equiv.apply_symm_apply] using ha

omit [NeZero width] [NeZero height] in
/-- The native two-plaquette block has exactly six physical sites. Source: SCP10, lines
2271–2305. -/
theorem twoPlaquetteTorusRegion_card :
    (twoPlaquetteTorusRegion (width := width) (height := height)).card = 6 := by
  rw [← Fintype.card_coe, ← Fintype.card_congr twoPlaquetteTorusVertexEquiv]
  rfl

/-- The actual six-site set is the coordinate rectangle of width three and height two. Source:
SCP10, lines 2271–2305. -/
theorem twoPlaquetteTorusRegion_eq_rectangle :
    twoPlaquetteTorusRegion (width := width) (height := height) =
      torusContiguousRectangle 0 0 3 2 := by
  ext v
  constructor
  · intro hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    rw [mem_torusContiguousRectangle]
    change 0 ≤ (twoPlaquetteX i : ZMod width).val ∧
      (twoPlaquetteX i : ZMod width).val < 3 ∧
      0 ≤ (twoPlaquetteY i : ZMod height).val ∧ (twoPlaquetteY i : ZMod height).val < 2
    rw [ZMod.val_natCast_of_lt (by have := twoPlaquetteX_lt (width := width) i; omega),
      ZMod.val_natCast_of_lt (by have := twoPlaquetteY_lt (height := height) i; omega)]
    exact (by decide : ∀ j : Fin 6, 0 ≤ twoPlaquetteX j ∧ twoPlaquetteX j < 3 ∧
      0 ≤ twoPlaquetteY j ∧ twoPlaquetteY j < 2) i
  · intro hv
    rw [mem_torusContiguousRectangle] at hv
    obtain ⟨i, hx, hy⟩ := (by decide : ∀ x : Fin 3, ∀ y : Fin 2,
      ∃ i : Fin 6, twoPlaquetteX i = x.val ∧ twoPlaquetteY i = y.val)
      ⟨v.1.val, by omega⟩ ⟨v.2.val, by omega⟩
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_univ _, ?_⟩
    apply Prod.ext
    · change (twoPlaquetteX i : ZMod width) = v.1
      rw [hx, ZMod.natCast_zmod_val]
    · change (twoPlaquetteY i : ZMod height) = v.2
      rw [hy, ZMod.natCast_zmod_val]

/-- The two actual non-tree internal bonds, retaining the native endpoint order. -/
noncomputable def twoPlaquetteTorusCycleBond (i : Fin 2) :
    {e : {e : Edge (torusGraph width height) //
      e.1.1 ∈ twoPlaquetteTorusRegion ∧ e.1.2 ∈ twoPlaquetteTorusRegion} //
      ¬ twoPlaquetteTorusTree.Adj ⟨e.1.1.1, e.2.1⟩ ⟨e.1.1.2, e.2.2⟩} := by
  let e := Edge.equiv (twoPlaquetteTorusIso (width := width) (height := height))
    (twoPlaquetteCycleBond i)
  refine ⟨inducedRegionEdgeEquiv twoPlaquetteTorusRegion e, ?_⟩
  change ¬ twoPlaquetteTorusTree.Adj e.1.1 e.1.2
  exact (Edge.comap_adj_map_iff (twoPlaquetteTorusIso (width := width) (height := height))
    twoPlaquetteTree (twoPlaquetteCycleBond i)).not.mpr (twoPlaquetteCycleBond_not_tree i)

/-- The actual leftmost and middle vertical non-tree bonds are distinct. Source: SCP10, lines
2271–2305. -/
theorem twoPlaquetteTorusCycleBond_injective :
    Function.Injective (twoPlaquetteTorusCycleBond (width := width) (height := height)) := by
  intro i j h
  apply twoPlaquetteCycleBond_injective
  apply (Edge.equiv (twoPlaquetteTorusIso (width := width) (height := height))).injective
  apply (inducedRegionEdgeEquiv twoPlaquetteTorusRegion).injective
  exact congrArg Subtype.val h

/-- The actual induced six-site torus region has exactly seven internal bonds. Source: SCP10,
lines 2271–2305. -/
theorem twoPlaquetteTorusRegion_card_internalEdges :
    Fintype.card {e : Edge (torusGraph width height) //
      e.1.1 ∈ twoPlaquetteTorusRegion ∧ e.1.2 ∈ twoPlaquetteTorusRegion} = 7 := by
  rw [← Fintype.card_congr (inducedRegionEdgeEquiv twoPlaquetteTorusRegion),
    ← Fintype.card_congr (Edge.equiv (twoPlaquetteTorusIso (width := width) (height := height)))]
  exact twoPlaquetteGraph_card_edges

/-- The actual fixed spanning tree has exactly five bonds. Source: SCP10, lines 2271–2305. -/
theorem twoPlaquetteTorusTree_card_edges :
    Fintype.card (Edge (twoPlaquetteTorusTree (width := width) (height := height))) = 5 := by
  change Fintype.card (Edge (twoPlaquetteTree.comap
    (twoPlaquetteTorusVertexEquiv (width := width) (height := height)).symm)) = 5
  rw [Fintype.card_congr (Edge.equiv (SimpleGraph.Iso.comap
    twoPlaquetteTorusVertexEquiv.symm twoPlaquetteTree))]
  exact twoPlaquetteTree_card_edges

/-- The actual induced six-site torus region is connected. Source: SCP10, lines 2271–2305. -/
theorem twoPlaquetteTorusRegion_connected :
    ((torusGraph width height).induce
      (twoPlaquetteTorusRegion (width := width) (height := height) :
        Set (TorusVertex width height))).Connected :=
  twoPlaquetteTorusTree_isTree.connected.mono twoPlaquetteTorusTree_le

/-- The two actual non-tree bonds point upward at horizontal coordinates zero and one. Source:
SCP10, lines 2271–2305. -/
theorem twoPlaquetteTorusCycleBond_endpoints (i : Fin 2) :
    (twoPlaquetteTorusCycleBond (width := width) (height := height) i).1.1.1.1 =
      ((i.val : ZMod width), 0) ∧
    (twoPlaquetteTorusCycleBond (width := width) (height := height) i).1.1.1.2 =
      ((i.val : ZMod width), 1) := by
  have hlt : ∀ j : Fin 2,
      (twoPlaquetteTorusVertexEquiv (width := width) (height := height))
        (twoPlaquetteCycleBond j).1.1 <
      twoPlaquetteTorusVertexEquiv (twoPlaquetteCycleBond j).1.2 := by
    intro j
    change toLex ((twoPlaquetteTorusVertex (twoPlaquetteCycleBond j).1.1).1.val,
      (twoPlaquetteTorusVertex (twoPlaquetteCycleBond j).1.1).2.val) <
      toLex ((twoPlaquetteTorusVertex (twoPlaquetteCycleBond j).1.2).1.val,
        (twoPlaquetteTorusVertex (twoPlaquetteCycleBond j).1.2).2.val)
    fin_cases j <;> simp [twoPlaquetteCycleBond, twoPlaquetteTorusVertex,
      twoPlaquetteX, twoPlaquetteY, Prod.Lex.toLex_lt_toLex, ZMod.val_one]
  change (Edge.map twoPlaquetteTorusIso (twoPlaquetteCycleBond i)).1.1.1 = _ ∧
    (Edge.map twoPlaquetteTorusIso (twoPlaquetteCycleBond i)).1.2.1 = _
  have hi := hlt i
  change (twoPlaquetteTorusIso (width := width) (height := height)).toEquiv
    (twoPlaquetteCycleBond i).1.1 < twoPlaquetteTorusIso.toEquiv
      (twoPlaquetteCycleBond i).1.2 at hi
  simp only [Edge.map, Edge.ofAdj, dite_eq_left hi]
  fin_cases i <;> simp [twoPlaquetteTorusIso, twoPlaquetteTorusVertexEquiv,
    twoPlaquetteCycleBond, twoPlaquetteTorusVertex, twoPlaquetteX, twoPlaquetteY]
end TNLean.PEPS

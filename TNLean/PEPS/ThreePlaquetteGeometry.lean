/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.EdgeMapSubgraph
import TNLean.PEPS.TranslatedTwoPlaquetteGeometry

/-!
# An actual translated strip of three torus plaquettes

Eight sites are numbered along the path through the lower row from left to
right, then through the upper row from right to left. The seven path bonds
are all six horizontal bonds and the rightmost vertical bond. The three
remaining vertical bonds are explicit distinct non-tree internal coordinates.
The numbering identifies this graph with the actual induced torus rectangle.

Source: SCP10, arXiv:1001.3807, adjacent fluxes and joint measurement in the
braiding passage, lines 2380–2415. The three-plaquette strip is an auxiliary
finite geometry for simultaneous operations on three flux coordinates.

**Scope restriction (eight-site strip):** The horizontal period is at least
five and the vertical period at least three. All translated positions, including
both seams, are allowed. No string braiding or parent-Hamiltonian assertion is
made; see `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
namespace TNLean.PEPS

private def stripGraph : SimpleGraph (Fin 8) :=
  SimpleGraph.pathGraph 8 ⊔ SimpleGraph.fromEdgeSet {s(0, 7), s(1, 6), s(2, 5)}
private def stripTree : SimpleGraph (Fin 8) := SimpleGraph.pathGraph 8
private instance stripPathDecidableAdj : DecidableRel (SimpleGraph.pathGraph 8).Adj :=
  fun i j => decidable_of_iff (i.val + 1 = j.val ∨ j.val + 1 = i.val)
    SimpleGraph.pathGraph_adj.symm
private instance stripGraphDecidableAdj : DecidableRel stripGraph.Adj := by
  unfold stripGraph
  infer_instance
private instance stripTreeDecidableAdj : DecidableRel stripTree.Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.pathGraph 8).Adj)
private theorem stripTree_isTree : stripTree.IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨SimpleGraph.pathGraph_connected 7, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  decide
private def stripX : Fin 8 → ℕ := ![0, 1, 2, 3, 3, 2, 1, 0]
private def stripY : Fin 8 → ℕ := ![0, 0, 0, 0, 1, 1, 1, 1]
private def stripCycle (i : Fin 3) : Edge stripGraph :=
  ![⟨(0, 7), by decide, by simp [stripGraph]⟩,
    ⟨(1, 6), by decide, by simp [stripGraph]⟩,
    ⟨(2, 5), by decide, by simp [stripGraph]⟩] i
private theorem stripCycle_not_tree (i : Fin 3) :
    ¬ stripTree.Adj (stripCycle i).1.1 (stripCycle i).1.2 := by
  fin_cases i <;> decide
private theorem stripCycle_injective : Function.Injective stripCycle := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [stripCycle]

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (4 < width)] [Fact (2 < height)]
local instance threePlaquetteWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 4 < width); omega⟩
local instance threePlaquetteHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height

private def originVertex (i : Fin 8) : X := (stripX i, stripY i)
omit [NeZero width] in
private theorem x_lt (i : Fin 8) : stripX i + 1 < width := by
  have := Fact.out (p := 4 < width)
  have := (by decide : ∀ j, stripX j ≤ 3) i
  omega
omit [NeZero height] in
private theorem y_lt (i : Fin 8) : stripY i + 1 < height := by
  have := Fact.out (p := 2 < height)
  have := (by decide : ∀ j, stripY j ≤ 1) i
  omega
private theorem cast_eq {n a b : ℕ} (ha : a < n) (hb : b < n) :
    (a : ZMod n) = (b : ZMod n) ↔ a = b := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

omit [NeZero width] [NeZero height] in
private theorem originVertex_injective :
    Function.Injective (originVertex (width := width) (height := height)) := by
  intro i j hij
  have hx := congrArg Prod.fst hij
  have hy := congrArg Prod.snd hij
  change (stripX i : ZMod width) = (stripX j : ZMod width) at hx
  change (stripY i : ZMod height) = (stripY j : ZMod height) at hy
  have hx' := (cast_eq (by have := x_lt (width := width) i; omega)
    (by have := x_lt (width := width) j; omega)).mp hx
  have hy' := (cast_eq (by have := y_lt (height := height) i; omega)
    (by have := y_lt (height := height) j; omega)).mp hy
  exact (by decide : Function.Injective (fun k => (stripX k, stripY k))) (Prod.ext hx' hy')
private theorem originVertex_adj_iff (i j : Fin 8) :
    (Γₜ).Adj (originVertex i) (originVertex j) ↔ stripGraph.Adj i j := by
  have hx (i : Fin 8) : stripX i < width := by have := x_lt (width := width) i; omega
  have hy (i : Fin 8) : stripY i < height := by have := y_lt (height := height) i; omega
  change ((stripY i : ZMod height) = (stripY j : ZMod height) ∧
    ((stripX i : ZMod width) + 1 = (stripX j : ZMod width) ∨
      (stripX j : ZMod width) + 1 = (stripX i : ZMod width))) ∨
    ((stripX i : ZMod width) = (stripX j : ZMod width) ∧
    ((stripY i : ZMod height) + 1 = (stripY j : ZMod height) ∨
      (stripY j : ZMod height) + 1 = (stripY i : ZMod height))) ↔ _
  rw [show (stripX i : ZMod width) + 1 = (↑(stripX i + 1)) by simp,
    show (stripX j : ZMod width) + 1 = (↑(stripX j + 1)) by simp,
    show (stripY i : ZMod height) + 1 = (↑(stripY i + 1)) by simp,
    show (stripY j : ZMod height) + 1 = (↑(stripY j + 1)) by simp]
  rw [cast_eq (hy i) (hy j), cast_eq (x_lt i) (hx j), cast_eq (x_lt j) (hx i),
    cast_eq (hx i) (hx j), cast_eq (y_lt i) (hy j), cast_eq (y_lt j) (hy i)]
  exact (by decide : ∀ a b : Fin 8,
    (stripY a = stripY b ∧ (stripX a + 1 = stripX b ∨ stripX b + 1 = stripX a)) ∨
    (stripX a = stripX b ∧ (stripY a + 1 = stripY b ∨ stripY b + 1 = stripY a)) ↔
    stripGraph.Adj a b) i j

/-- The eight native sites, numbered along the prescribed spanning path.
Auxiliary to SCP10, braiding passage, lines 2380–2415. -/
def translatedThreePlaquetteVertex (v : X) (i : Fin 8) : X :=
  translate v.1 v.2 (originVertex i)

/-- The actual translated eight-site region of three adjacent plaquettes.
Auxiliary to SCP10, braiding passage, lines 2380–2415. -/
def translatedThreePlaquetteRegion (v : X) : Finset X :=
  Finset.univ.image (translatedThreePlaquetteVertex v)

/-- The derived bijection between path labels and actual physical sites.
Auxiliary to SCP10, braiding passage, lines 2380–2415. -/
def translatedThreePlaquetteVertexEquiv (v : X) :
    Fin 8 ≃ {x : X // x ∈ translatedThreePlaquetteRegion v} :=
  Equiv.ofBijective (fun i => ⟨translatedThreePlaquetteVertex v i,
    Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩) (by
    constructor
    · intro i j h
      exact ((translate v.1 v.2).injective.comp originVertex_injective)
        (congrArg Subtype.val h)
    · intro x
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp x.2
      exact ⟨i, Subtype.ext hi⟩)
private def stripIso (v : X) :
    stripGraph ≃g (Γₜ).induce (translatedThreePlaquetteRegion v : Set X) where
  __ := translatedThreePlaquetteVertexEquiv v
  map_rel_iff' := by
    intro i j
    exact (translate v.1 v.2).map_rel_iff'.trans (originVertex_adj_iff i j)

/-- The actual spanning path containing all horizontal bonds and the rightmost vertical bond.
Auxiliary to SCP10, braiding passage, lines 2380–2415. -/
def translatedThreePlaquetteTree (v : X) :
    SimpleGraph {x : X // x ∈ translatedThreePlaquetteRegion v} :=
  stripTree.comap (translatedThreePlaquetteVertexEquiv v).symm
instance threePlaquetteTreeDecidableAdj (v : X) :
    DecidableRel (translatedThreePlaquetteTree v).Adj := by
  unfold translatedThreePlaquetteTree
  infer_instance

/-- The prescribed seven-bond spanning path is a tree.
Auxiliary to SCP10, braiding passage, lines 2380–2415. -/
theorem translatedThreePlaquetteTree_isTree (v : X) :
    (translatedThreePlaquetteTree v).IsTree :=
  (SimpleGraph.Iso.isTree_iff (SimpleGraph.Iso.comap
    (translatedThreePlaquetteVertexEquiv v).symm stripTree)).mpr stripTree_isTree

/-- The prescribed tree lies in the actual induced torus graph.
Auxiliary to SCP10, braiding passage, lines 2380–2415. -/
theorem translatedThreePlaquetteTree_le (v : X) :
    translatedThreePlaquetteTree v ≤
      (Γₜ).induce (translatedThreePlaquetteRegion v : Set X) := by
  intro x y h
  have ht : stripGraph.Adj ((translatedThreePlaquetteVertexEquiv v).symm x)
      ((translatedThreePlaquetteVertexEquiv v).symm y) :=
    (show stripTree ≤ stripGraph from le_sup_left) h
  have ha := (stripIso v).map_rel_iff'.mpr ht
  change (Γₜ).Adj
    ((translatedThreePlaquetteVertexEquiv v)
      ((translatedThreePlaquetteVertexEquiv v).symm x)).1
    ((translatedThreePlaquetteVertexEquiv v)
      ((translatedThreePlaquetteVertexEquiv v).symm y)).1 at ha
  change (Γₜ).Adj x.1 y.1
  simpa only [Equiv.apply_symm_apply] using ha

/-- The actual induced eight-site region is connected.
Auxiliary to SCP10, braiding passage, lines 2380–2415. -/
theorem translatedThreePlaquetteRegion_connected (v : X) :
    ((Γₜ).induce (translatedThreePlaquetteRegion v : Set X)).Connected :=
  (translatedThreePlaquetteTree_isTree v).connected.mono (translatedThreePlaquetteTree_le v)

/-- The translated region has exactly eight sites.
Auxiliary to SCP10, braiding passage, lines 2380–2415. -/
theorem translatedThreePlaquetteRegion_card (v : X) :
    (translatedThreePlaquetteRegion v).card = 8 := by
  rw [← Fintype.card_coe, ← Fintype.card_congr (translatedThreePlaquetteVertexEquiv v)]
  rfl

/-- The three actual ordered non-tree bonds, from left to right.
Auxiliary to SCP10, braiding passage, lines 2380–2415. -/
def translatedThreePlaquetteCycleBond (v : X) (i : Fin 3) :
    {e : {e : Edge Γₜ // e.1.1 ∈ translatedThreePlaquetteRegion v ∧
      e.1.2 ∈ translatedThreePlaquetteRegion v} //
      ¬ (translatedThreePlaquetteTree v).Adj ⟨e.1.1.1, e.2.1⟩ ⟨e.1.1.2, e.2.2⟩} := by
  let e := Edge.equiv (stripIso v) (stripCycle i)
  refine ⟨inducedRegionEdgeEquiv (translatedThreePlaquetteRegion v) e, ?_⟩
  change ¬ (translatedThreePlaquetteTree v).Adj
    (Edge.map (stripIso v) (stripCycle i)).1.1
    (Edge.map (stripIso v) (stripCycle i)).1.2
  exact (Edge.comap_adj_map_iff (stripIso v) stripTree (stripCycle i)).not.mpr
    (stripCycle_not_tree i)

/-- The three chosen non-tree vertical bonds are distinct.
Auxiliary to SCP10, braiding passage, lines 2380–2415. -/
theorem translatedThreePlaquetteCycleBond_injective (v : X) :
    Function.Injective (translatedThreePlaquetteCycleBond v) := by
  intro i j h
  apply stripCycle_injective
  apply (Edge.equiv (stripIso v)).injective
  apply (inducedRegionEdgeEquiv (translatedThreePlaquetteRegion v)).injective
  exact congrArg Subtype.val h

/-- Each chosen ordered bond is the indicated upward native torus step.
Auxiliary to SCP10, braiding passage, lines 2380–2415. -/
theorem translatedThreePlaquetteCycleBond_eq_up (v : X) (i : Fin 3) :
    (translatedThreePlaquetteCycleBond v i).1.1 =
      Edge.ofAdj (torusGraph_adj_up (v.1 + (i.val : ZMod width)) v.2) := by
  change (inducedRegionEdgeEquiv (translatedThreePlaquetteRegion v)
    (Edge.map (stripIso v) (stripCycle i))).1 = _
  fin_cases i <;>
    simp [stripCycle, Edge.map, Edge.ofAdj, inducedRegionEdgeEquiv, stripIso,
      translatedThreePlaquetteVertexEquiv, translatedThreePlaquetteVertex,
      originVertex, stripX, stripY, add_comm] <;> split_ifs <;> rfl

/-- The actual induced strip has ten internal bonds.
Auxiliary to SCP10, braiding passage, lines 2380–2415. -/
theorem translatedThreePlaquetteRegion_card_internalEdges (v : X) :
    Fintype.card {e : Edge Γₜ // e.1.1 ∈ translatedThreePlaquetteRegion v ∧
      e.1.2 ∈ translatedThreePlaquetteRegion v} = 10 := by
  rw [← Fintype.card_congr (inducedRegionEdgeEquiv (translatedThreePlaquetteRegion v)),
    ← Fintype.card_congr (Edge.equiv (stripIso v)),
    Fintype.card_congr (orderedEdgeEquivEdgeSet (Γ := stripGraph))]
  decide

/-- The actual site set is the cyclic rectangle of width four and height two.
Auxiliary to SCP10, braiding passage, lines 2380–2415. -/
theorem translatedThreePlaquetteRegion_eq_arcRectangle (v : X) :
    translatedThreePlaquetteRegion v = torusArcRectangle v 4 2 := by
  ext w
  constructor
  · intro hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
    rw [mem_torusArcRectangle]
    change ((stripX i : ZMod width) + v.1 - v.1).val < 4 ∧
      ((stripY i : ZMod height) + v.2 - v.2).val < 2
    rw [add_sub_cancel_right, add_sub_cancel_right,
      ZMod.val_natCast_of_lt (by have := x_lt (width := width) i; omega),
      ZMod.val_natCast_of_lt (by have := y_lt (height := height) i; omega)]
    exact (by decide : ∀ j : Fin 8, stripX j < 4 ∧ stripY j < 2) i
  · intro hw
    rw [mem_torusArcRectangle] at hw
    obtain ⟨i, hx, hy⟩ := (by decide : ∀ x : Fin 4, ∀ y : Fin 2,
      ∃ i : Fin 8, stripX i = x.val ∧ stripY i = y.val)
      ⟨(w.1 - v.1).val, hw.1⟩ ⟨(w.2 - v.2).val, hw.2⟩
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_univ _, ?_⟩
    apply Prod.ext
    · change (stripX i : ZMod width) + v.1 = w.1
      rw [hx, ZMod.natCast_zmod_val, sub_add_cancel]
    · change (stripY i : ZMod height) + v.2 = w.2
      rw [hy, ZMod.natCast_zmod_val, sub_add_cancel]

end TNLean.PEPS

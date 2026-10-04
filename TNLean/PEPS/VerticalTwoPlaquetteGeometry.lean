/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TranslatedTwoPlaquetteGeometry

/-!
# The translated vertical two-plaquette block

Exchanging the two torus coordinates carries the established three-by-two
block to an actual two-by-three induced region. Its spanning path runs
(0,0),(0,1),(0,2),(1,2),(1,1),(1,0), relative to the starting position.
The two remaining bonds are the rightward steps at rows zero and one.

Source: SCP10, arXiv:1001.3807, Theorem 6.16, lines 2271–2305.
This auxiliary finite-torus realization assumes width at least three and
height at least four. Both periodic seams are included; no Hamiltonian
statement is made. See `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (3 < height)]
local instance verticalTwoWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance verticalTwoHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 3 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height

/-- Coordinate exchange is an actual torus graph isomorphism.
Source: SCP10, rotated local construction in Theorem 6.16, lines 2271–2305. -/
def torusCoordinateSwap : torusGraph height width ≃g Γₜ where
  __ := Equiv.prodComm (ZMod height) (ZMod width)
  map_rel_iff' := by
    intro v w
    change (torusVerticalNeighbor v w ∨ torusHorizontalNeighbor v w) ↔ _
    exact or_comm

/-- The actual translated two-by-three region, obtained by coordinate exchange.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
def verticalTwoPlaquetteRegion (v : X) : Finset X :=
  Region.map torusCoordinateSwap (translatedTwoPlaquetteRegion (width := height)
    (height := width) v.swap)

private theorem swap_bijOn (v : X) :
    Set.BijOn torusCoordinateSwap
      (translatedTwoPlaquetteRegion (width := height) (height := width) v.swap : Set _)
      (verticalTwoPlaquetteRegion v : Set X) := by
  refine ⟨fun x hx => (mem_Region_map_apply _ _ _).mpr hx,
    fun _ _ _ _ h => torusCoordinateSwap.injective h, ?_⟩
  intro x hx
  exact ⟨torusCoordinateSwap.symm x, (mem_Region_map _ _ _).mp hx,
    torusCoordinateSwap.apply_symm_apply x⟩

/-- The six-site graph is the literal induced vertical region.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
def verticalTwoPlaquetteIso (v : X) :
    twoPlaquetteGraph ≃g (Γₜ).induce (verticalTwoPlaquetteRegion v : Set X) :=
  (translatedTwoPlaquetteIso (width := height) (height := width) v.swap).trans
    (torusCoordinateSwap.induce (swap_bijOn v))

/-- The fixed five-edge spanning path in the actual induced vertical region.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
def verticalTwoPlaquetteTree (v : X) :
    SimpleGraph {x : X // x ∈ verticalTwoPlaquetteRegion v} :=
  twoPlaquetteTree.comap (verticalTwoPlaquetteIso v).symm

noncomputable instance verticalTwoPlaquetteTreeDecidableAdj (v : X) :
    DecidableRel (verticalTwoPlaquetteTree v).Adj := by
  unfold verticalTwoPlaquetteTree
  infer_instance

/-- The transported five-edge path is a spanning tree.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem verticalTwoPlaquetteTree_isTree (v : X) :
    (verticalTwoPlaquetteTree v).IsTree :=
  (SimpleGraph.Iso.isTree_iff (SimpleGraph.Iso.comap
    (verticalTwoPlaquetteIso v).symm.toEquiv twoPlaquetteTree)).mpr twoPlaquetteTree_isTree

/-- The fixed path lies in the actual induced torus graph.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem verticalTwoPlaquetteTree_le (v : X) :
    verticalTwoPlaquetteTree v ≤ (Γₜ).induce (verticalTwoPlaquetteRegion v : Set X) := by
  intro x y h
  exact (verticalTwoPlaquetteIso v).symm.map_rel_iff'.mp (twoPlaquetteTree_le h)

/-- The physical region has exactly six sites.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem verticalTwoPlaquetteRegion_card (v : X) :
    (verticalTwoPlaquetteRegion v).card = 6 := by
  have h := Fintype.card_congr (verticalTwoPlaquetteIso v).toEquiv
  simpa only [Finset.coe_sort_coe, Fintype.card_fin, Fintype.card_coe] using h.symm

/-- The two derived non-tree bonds, transported with their endpoint sorting.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
def verticalTwoPlaquetteCycleBond (v : X) (i : Fin 2) :
    {e : {e : Edge Γₜ // e.1.1 ∈ verticalTwoPlaquetteRegion v ∧
      e.1.2 ∈ verticalTwoPlaquetteRegion v} //
      ¬ (verticalTwoPlaquetteTree v).Adj ⟨e.1.1.1, e.2.1⟩ ⟨e.1.1.2, e.2.2⟩} := by
  let e := Edge.equiv (verticalTwoPlaquetteIso v) (twoPlaquetteCycleBond i)
  refine ⟨inducedRegionEdgeEquiv (verticalTwoPlaquetteRegion v) e, ?_⟩
  change ¬ (verticalTwoPlaquetteTree v).Adj e.1.1 e.1.2
  exact (Edge.comap_adj_map_iff (verticalTwoPlaquetteIso v)
    twoPlaquetteTree (twoPlaquetteCycleBond i)).not.mpr (twoPlaquetteCycleBond_not_tree i)

/-- The two horizontal chords are distinct, including at either seam.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem verticalTwoPlaquetteCycleBond_injective (v : X) :
    Function.Injective (verticalTwoPlaquetteCycleBond v) := by
  intro i j h
  apply twoPlaquetteCycleBond_injective
  apply (Edge.equiv (verticalTwoPlaquetteIso v)).injective
  apply (inducedRegionEdgeEquiv (verticalTwoPlaquetteRegion v)).injective
  exact congrArg Subtype.val h

/-- The numbering is the literal translated vertical five-edge path.
Source: SCP10, rotated construction in Theorem 6.16, lines 2271–2305. -/
theorem verticalTwoPlaquetteIso_apply (v : X) (i : Fin 6) :
    (verticalTwoPlaquetteIso v i).1 =
      (v.1 + ((![0, 0, 0, 1, 1, 1] i : ℕ) : ZMod width),
       v.2 + ((![0, 1, 2, 2, 1, 0] i : ℕ) : ZMod height)) := by
  change (((![0, 0, 0, 1, 1, 1] i : ℕ) : ZMod width) + v.1,
    ((![0, 1, 2, 2, 1, 0] i : ℕ) : ZMod height) + v.2) = _
  simp only [add_comm]


/-- Each selected chord is the actual rightward step, with native sorting retained.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem verticalTwoPlaquetteCycleBond_eq_right (v : X) (i : Fin 2) :
    (verticalTwoPlaquetteCycleBond v i).1.1 =
      Edge.ofAdj (torusGraph_adj_right v.1 (v.2 + (i.val : ZMod height))) := by
  symm
  apply Edge.ofAdj_eq_of_endpoints
  have he := Edge.map_endpoints (verticalTwoPlaquetteIso v) (twoPlaquetteCycleBond i)
  have hlo : (verticalTwoPlaquetteIso v (twoPlaquetteCycleBond i).1.1).1 =
      (v.1, v.2 + (i.val : ZMod height)) := by
    rw [verticalTwoPlaquetteIso_apply]
    fin_cases i <;> simp [twoPlaquetteCycleBond]
  have hhi : (verticalTwoPlaquetteIso v (twoPlaquetteCycleBond i).1.2).1 =
      (v.1 + 1, v.2 + (i.val : ZMod height)) := by
    rw [verticalTwoPlaquetteIso_apply]
    fin_cases i <;> simp [twoPlaquetteCycleBond]
  rcases he with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · exact Or.inl ⟨by simpa only [verticalTwoPlaquetteCycleBond, inducedRegionEdgeEquiv,
        Edge.equiv_apply, Equiv.coe_fn_mk, ← hlo] using (congrArg Subtype.val h₁).symm,
      by simpa only [verticalTwoPlaquetteCycleBond, inducedRegionEdgeEquiv,
        Edge.equiv_apply, Equiv.coe_fn_mk, ← hhi] using (congrArg Subtype.val h₂).symm⟩
  · exact Or.inr ⟨by simpa only [verticalTwoPlaquetteCycleBond, inducedRegionEdgeEquiv,
        Edge.equiv_apply, Equiv.coe_fn_mk, ← hlo] using (congrArg Subtype.val h₂).symm,
      by simpa only [verticalTwoPlaquetteCycleBond, inducedRegionEdgeEquiv,
        Edge.equiv_apply, Equiv.coe_fn_mk, ← hhi] using (congrArg Subtype.val h₁).symm⟩

end TNLean.PEPS

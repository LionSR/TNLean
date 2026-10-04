/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.IntegerCellExteriorCollar
import TNLean.PEPS.IntegerCellBoundaryContour
import TNLean.PEPS.TorusRegionIntegerCellLift
import TNLean.PEPS.TorusComplementCycleWords
import TNLean.PEPS.TorusExteriorPathApproximation
import TNLean.PEPS.TorusRegionBoundaryLift

/-!
# Complementary path replacement within the genuine exterior collar

The lifted endpoints of an interior boundary route belong to the exterior
integer-cell band. A continuous path between them in the genuine collar
projects outside the actual torus region and gives an induced-complement walk
with exactly the original route's crossing numbers.

**Scope restriction (simple torus graph):** Both torus periods are at least
three. The intermediate path-replacement statements expose the collar premises;
the final theorem derives them from actual simple connectedness. The rooted
trees describe chosen paths and are independent of all closure labels. See
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, exterior replacement
in the proof of Theorem 6.9, local source lines 1935–1990.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

noncomputable section
open Set

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]

local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height

/-- A genuine collar path replaces an interior boundary route by an actual
complement walk with the same seam crossing numbers. No group label or
holonomy identity is assumed. Source: SCP10, Theorem 6.9,
lines 1935–1990; auxiliary geometric path replacement. -/
private theorem exists_complementWalk_of_integerCollar_joined
    (R : Finset X) (L : {v // v ∈ R} → ℤ × ℤ) (hL : IsTorusRegionIntegerLift R L)
    (hπ : ∀ x ∈ integerExteriorCollar (Finset.univ.image L),
      torusRealProjection width height x ∉ torusRegionRealization R)
    (hjoin : ∀ a b : integerExteriorBand (Finset.univ.image L),
      JoinedIn (integerExteriorCollar (Finset.univ.image L))
        (integerCellCenter a.1) (integerCellCenter b.1))
    {v₀ v : {v // v ∈ R}}
    (p : ((Γₜ).induce (R : Set X)).Walk v₀ v)
    (w₀ w : {v // v ∈ Finset.univ \ R})
    (h₀ : (Γₜ).Adj v₀.1 w₀.1) (h : (Γₜ).Adj v.1 w.1) :
    ∃ q : ((Γₜ).induce ((Finset.univ \ R : Finset X) : Set X)).Walk w₀ w,
      torusWalkWinding (q.map ⟨Subtype.val, fun {_ _} h => h⟩) =
        torusWalkWinding
          ((SimpleGraph.Walk.cons h₀.symm (p.map ⟨Subtype.val, fun {_ _} h => h⟩)).append
            (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil)) := by
  obtain ⟨a, b, ha, hb, hca, hcb, hw⟩ := exists_exterior_integerEndpoints_of_regionWalk
    hL p w₀.1 w.1 (Finset.mem_sdiff.mp w₀.2).2 (Finset.mem_sdiff.mp w.2).2 h₀ h
  have hc : integerCellCenter a ∈ integerExteriorCollar (Finset.univ.image L) ∧
      integerCellCenter b ∈ integerExteriorCollar (Finset.univ.image L) := by
    simpa only [integerExteriorCollar, integerCellCenter,
      integerClosedCellUnion_image_eq_torusRegionPlanarRealization] using And.intro hca hcb
  obtain ⟨γ, hγ⟩ := hjoin
    ⟨a, (integerCellCenter_mem_exteriorCollar_iff _ _).mp hc.1⟩
    ⟨b, (integerCellCenter_mem_exteriorCollar_iff _ _).mp hc.2⟩
  obtain ⟨q, hq⟩ := exists_complementWalk_of_exterior_planePath R w₀ w a b ha hb γ
    (fun t => hπ _ (hγ t))
  exact ⟨q, hq.trans hw.symm⟩

/-- Connectivity of the safe integer exterior graph supplies a genuine collar
path, hence an actual complementary walk with the same seam crossing numbers
as the interior boundary route. Source: SCP10, Theorem 6.9,
lines 1935–1990; auxiliary geometric path replacement. -/
theorem exists_complementWalk_of_integerExteriorCollarGraph_connected
    (R : Finset X) (L : {v // v ∈ R} → ℤ × ℤ) (hL : IsTorusRegionIntegerLift R L)
    (hπ : ∀ x ∈ integerExteriorCollar (Finset.univ.image L),
      torusRealProjection width height x ∉ torusRegionRealization R)
    (hconn : (integerExteriorCollarGraph (Finset.univ.image L)).Connected)
    {v₀ v : {v // v ∈ R}}
    (p : ((Γₜ).induce (R : Set X)).Walk v₀ v)
    (w₀ w : {v // v ∈ Finset.univ \ R})
    (h₀ : (Γₜ).Adj v₀.1 w₀.1) (h : (Γₜ).Adj v.1 w.1) :
    ∃ q : ((Γₜ).induce ((Finset.univ \ R : Finset X) : Set X)).Walk w₀ w,
      torusWalkWinding (q.map ⟨Subtype.val, fun {_ _} h => h⟩) =
        torusWalkWinding
          ((SimpleGraph.Walk.cons h₀.symm (p.map ⟨Subtype.val, fun {_ _} h => h⟩)).append
            (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil)) := by
  exact exists_complementWalk_of_integerCollar_joined R L hL hπ
    (fun a b => joinedIn_integerExteriorCollar_of_reachable _ (hconn.preconnected a b))
    p w₀ w h₀ h

private def regionTreeInducedWalk (R : Finset X)
    (T : SimpleGraph {v : X // v ∈ R}) (hT : T ≤ (Γₜ).induce (R : Set X))
    (htree : T.IsTree) (v w : {v // v ∈ R}) :
    ((Γₜ).induce (R : Set X)).Walk v w :=
  (Classical.choose (htree.connected.exists_isPath v w)).map (SimpleGraph.Hom.ofLE hT)

private theorem regionTreeInducedWalk_map (R : Finset X)
    (T : SimpleGraph {v : X // v ∈ R}) (hT : T ≤ (Γₜ).induce (R : Set X))
    (htree : T.IsTree) (v w : {v // v ∈ R}) :
    (regionTreeInducedWalk R T hT htree v w).map ⟨Subtype.val, fun {_ _} h => h⟩ =
      regularRegionTreeWalk R T hT htree v w := by
  rw [regionTreeInducedWalk, SimpleGraph.Walk.map_map]
  rfl

/-- The safe exterior graph yields complementary root loops for every native
boundary edge. They have exactly the crossing numbers of the two-tree boundary
routes and are chosen independently of all group-valued closure labels.
Source: SCP10, Theorem 6.9, lines 1935–1990; auxiliary geometric construction. -/
theorem exists_complementBoundaryLoops_of_integerExteriorCollarGraph_connected
    (R : Finset X) (L : {v // v ∈ R} → ℤ × ℤ) (hL : IsTorusRegionIntegerLift R L)
    (hπ : ∀ x ∈ integerExteriorCollar (Finset.univ.image L),
      torusRealProjection width height x ∉ torusRegionRealization R)
    (hconn : (integerExteriorCollarGraph (Finset.univ.image L)).Connected)
    (TR : SimpleGraph {v : X // v ∈ R})
    (TS : SimpleGraph {v : X // v ∈ Finset.univ \ R})
    (hTR : TR ≤ (Γₜ).induce (R : Set X))
    (hTS : TS ≤ (Γₜ).induce ((Finset.univ \ R : Finset X) : Set X))
    (htreeR : TR.IsTree) (htreeS : TS.IsTree)
    (oS : {v : X // v ∈ Finset.univ \ R})
    (f₀ : {e : Edge Γₜ // IsRegionBoundaryEdge R e}) :
    ∃ p : {e : Edge Γₜ // IsRegionBoundaryEdge R e} →
        ((Γₜ).induce ((Finset.univ \ R : Finset X) : Set X)).Walk oS oS,
      ∀ f, torusWalkWinding
          ((p f).map (SimpleGraph.Embedding.induce
            ((Finset.univ \ R : Finset X) : Set X)).toHom) =
        torusWalkWinding (torusBoundaryTreeRoute R TR TS hTR hTS htreeR htreeS oS f₀ f) := by
  classical
  have hf (f : {e : Edge Γₜ // IsRegionBoundaryEdge R e}) :
      ∃ p : ((Γₜ).induce ((Finset.univ \ R : Finset X) : Set X)).Walk oS oS,
        torusWalkWinding (p.map ⟨Subtype.val, fun {_ _} h => h⟩) =
          torusWalkWinding
            (torusBoundaryTreeRoute R TR TS hTR hTS htreeR htreeS oS f₀ f) := by
    let v₀ := regularBoundaryInsideVertex R f₀
    let v := regularBoundaryInsideVertex R f
    let w₀ := regularBoundaryOutsideVertex R f₀
    let w := regularBoundaryOutsideVertex R f
    let pR := regionTreeInducedWalk R TR hTR htreeR v₀ v
    let pS₀ := regionTreeInducedWalk (Finset.univ \ R) TS hTS htreeS oS w₀
    let pS := regionTreeInducedWalk (Finset.univ \ R) TS hTS htreeS w oS
    obtain ⟨q, hq⟩ := exists_complementWalk_of_integerExteriorCollarGraph_connected
      R L hL hπ hconn pR w₀ w
      (regularBoundaryCrossingAdj R f₀) (regularBoundaryCrossingAdj R f)
    refine ⟨pS₀.append (q.append pS), ?_⟩
    simp only [SimpleGraph.Walk.map_append, torusWalkWinding_append]
    rw [hq]
    simp only [torusBoundaryTreeRoute, regularBoundaryTreeRoute, regularBoundaryRoute,
      torusWalkWinding_append, torusWalkWinding,
      pR, pS₀, pS, regionTreeInducedWalk_map]
    abel
  choose p hp using hf
  exact ⟨p, hp⟩

/-- Actual simple connectedness supplies complementary root loops with the
winding of every two-tree boundary route. No collar connectivity, exterior path,
or winding identity is supplied. The loops are independent of closure labels.
Source: SCP10, exterior construction in Theorem 6.9, lines 1935–1990. -/
theorem exists_complementBoundaryLoops_of_isSimplyConnected
    (R : Finset X) (hSC : IsSimplyConnected (torusRegionRealization R))
    (TR : SimpleGraph {v : X // v ∈ R})
    (TS : SimpleGraph {v : X // v ∈ Finset.univ \ R})
    (hTR : TR ≤ (Γₜ).induce (R : Set X))
    (hTS : TS ≤ (Γₜ).induce ((Finset.univ \ R : Finset X) : Set X))
    (htreeR : TR.IsTree) (htreeS : TS.IsTree)
    (oS : {v : X // v ∈ Finset.univ \ R})
    (f₀ : {e : Edge Γₜ // IsRegionBoundaryEdge R e}) :
    ∃ p : {e : Edge Γₜ // IsRegionBoundaryEdge R e} →
        ((Γₜ).induce ((Finset.univ \ R : Finset X) : Set X)).Walk oS oS,
      ∀ f, torusWalkWinding
          ((p f).map (SimpleGraph.Embedding.induce
            ((Finset.univ \ R : Finset X) : Set X)).toHom) =
        torusWalkWinding (torusBoundaryTreeRoute R TR TS hTR hTS htreeR htreeS oS f₀ f) := by
  obtain ⟨L, hL, hP, hπ⟩ :=
    exists_integerLift_simplyConnected_exteriorCollar_of_isSimplyConnected R hSC
  exact exists_complementBoundaryLoops_of_integerExteriorCollarGraph_connected R L hL hπ
    (integerExteriorCollarGraph_connected_of_isSimplyConnected _ hP)
    TR TS hTR hTS htreeR htreeS oS f₀

end TNLean.PEPS

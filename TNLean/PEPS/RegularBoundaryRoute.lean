/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularRegionCycleHolonomy
import TNLean.PEPS.RegionBlock.Insertion

/-!
# Actual boundary routes through two region trees

A crossing bond transports from the region endpoint to the complementary
endpoint. After the two normalized tree gauges, its multiplier is the
complementary endpoint gauge inverse, followed by the directed bond operator
and the region endpoint gauge. Two crossing bonds therefore determine an actual
closed walk through the two region trees whose holonomy is their relative
multiplier. This walk passes through the region; no complementary replacement
walk or equality of their holonomies is asserted.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, seam deformation,
lines 1622–1647, and accessible complement cycle records, lines 1935–1990.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

namespace TNLean.PEPS

variable {V : Type*} [LinearOrder V] {Γ : SimpleGraph V}
variable {G : Type*} [Group G]

/-- An induced-region walk has the same native holonomy after inclusion in
its ambient graph. Source: SCP10, actual region routes, lines 1935–1990. -/
theorem regularWalkHolonomy_inducedWalk (R : Finset V) (u : Edge Γ → G)
    {v w : {v : V // v ∈ R}} (p : (Γ.induce (R : Set V)).Walk v w) :
    regularWalkHolonomy (regularRegionInternalOperators R u) p =
      regularWalkHolonomy u (p.map (SimpleGraph.Embedding.induce (R : Set V)).toHom) := by
  have hstep {v w : {v : V // v ∈ R}} (h : (Γ.induce (R : Set V)).Adj v w) :
      regularDirectedTransport (regularRegionInternalOperators R u) h =
        regularDirectedTransport u
          ((SimpleGraph.Embedding.induce (R : Set V)).toHom.map_adj h) := by
    unfold regularDirectedTransport regularRegionInternalOperators Edge.ofAdj
    split_ifs <;> first | rfl | contradiction
  induction p with
  | nil => simp only [SimpleGraph.Walk.map_nil, regularWalkHolonomy_nil]
  | cons h p ih =>
    rw [SimpleGraph.Walk.map_cons, regularWalkHolonomy_cons,
      regularWalkHolonomy_cons, ih, hstep]

private def regionTreeHom (R : Finset V) (T : SimpleGraph {v : V // v ∈ R})
    (hT : T ≤ Γ.induce (R : Set V)) : T →g Γ where
  toFun := Subtype.val
  map_rel' := fun {_ _} h => hT h

/-- The unique tree path, read as an actual walk of the ambient graph.
Source: SCP10, tree blocking and boundary routes, lines 1765–1920 and 1935–1990. -/
noncomputable def regularRegionTreeWalk (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) (hT : T ≤ Γ.induce (R : Set V))
    (htree : T.IsTree) (v w : {v // v ∈ R}) : Γ.Walk v.1 w.1 :=
  (Classical.choose (htree.connected.exists_isPath v w)).map (regionTreeHom R T hT)

variable [Fintype G]

private theorem treeWalk_holonomy (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v // v ∈ R})
    (u : Edge Γ → G) {v w : {v // v ∈ R}} (p : T.Walk v w) :
    regularWalkHolonomy u (p.map (regionTreeHom R T hT)) =
      (regularRegionTreeGauge R T hT htree o u).1 w *
        ((regularRegionTreeGauge R T hT htree o u).1 v)⁻¹ := by
  have hstep {v w : {v // v ∈ R}} (h : T.Adj v w) (hΓ : Γ.Adj v.1 w.1) :
      regularDirectedTransport u hΓ =
        (regularRegionTreeGauge R T hT htree o u).1 w *
          ((regularRegionTreeGauge R T hT htree o u).1 v)⁻¹ := by
    rcases lt_or_gt_of_ne hΓ.ne with hvw | hwv
    · rw [regularDirectedTransport_of_lt u hΓ hvw]
      exact (regularRegionTreeGauge_gradient R T hT htree o u
        ⟨⟨(v.1, w.1), hvw, hT h⟩, v.2, w.2⟩ h).symm
    · rw [regularDirectedTransport_of_gt u hΓ hwv]
      simpa only [mul_inv_rev, inv_inv] using congrArg (fun z : G => z⁻¹)
        (regularRegionTreeGauge_gradient R T hT htree o u
          ⟨⟨(w.1, v.1), hwv, hT h.symm⟩, w.2, v.2⟩ h.symm).symm
  induction p with
  | nil => simp only [SimpleGraph.Walk.map_nil, regularWalkHolonomy_nil, mul_inv_cancel]
  | cons h p ih =>
    rw [SimpleGraph.Walk.map_cons, regularWalkHolonomy_cons, ih]
    simp only [regionTreeHom]
    rw [hstep h]
    group

/-- Tree transport is the endpoint gradient of the normalized native gauge.
Source: SCP10, tree blocking, lines 1765–1920. -/
theorem regularRegionTreeWalk_holonomy (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v // v ∈ R})
    (u : Edge Γ → G) (v w : {v // v ∈ R}) :
    regularWalkHolonomy u (regularRegionTreeWalk R T hT htree v w) =
      (regularRegionTreeGauge R T hT htree o u).1 w *
        ((regularRegionTreeGauge R T hT htree o u).1 v)⁻¹ :=
  treeWalk_holonomy R T hT htree o u _

/-- The actual closed route through two crossing bonds and three supplied
paths: first reach the reference crossing, enter the region, leave at the
second crossing, and return to the starting vertex. -/
def regularBoundaryRoute {o v₀ v w₀ w : V} (h₀ : Γ.Adj v₀ w₀) (h : Γ.Adj v w)
    (pS₀ : Γ.Walk o w₀) (pR : Γ.Walk v₀ v) (pS : Γ.Walk w o) : Γ.Walk o o :=
  pS₀.append (.cons h₀.symm (pR.append (.cons h pS)))

omit [Fintype G] in
/-- The transport of the constructed route is the actual ordered product of
its three path transports and its two crossing operators. -/
theorem regularBoundaryRoute_holonomy (u : Edge Γ → G) {o v₀ v w₀ w : V}
    (h₀ : Γ.Adj v₀ w₀) (h : Γ.Adj v w)
    (pS₀ : Γ.Walk o w₀) (pR : Γ.Walk v₀ v) (pS : Γ.Walk w o) :
    regularWalkHolonomy u (regularBoundaryRoute h₀ h pS₀ pR pS) =
      regularWalkHolonomy u pS * regularDirectedTransport u h *
        regularWalkHolonomy u pR * (regularDirectedTransport u h₀)⁻¹ *
          regularWalkHolonomy u pS₀ := by
  simp only [regularBoundaryRoute, regularWalkHolonomy_append,
    regularWalkHolonomy_cons, mul_assoc]
  rw [regularDirectedTransport_symm u h₀]

/-- The actual closed boundary route, with the three paths chosen in the two
region trees. This route includes an interior segment. Source: SCP10,
seam deformation and accessible cycles, lines 1622–1647 and 1935–1990. -/
noncomputable def regularBoundaryTreeRoute (R S : Finset V)
    (TR : SimpleGraph {v : V // v ∈ R}) (TS : SimpleGraph {v : V // v ∈ S})
    (hTR : TR ≤ Γ.induce (R : Set V)) (hTS : TS ≤ Γ.induce (S : Set V))
    (htreeR : TR.IsTree) (htreeS : TS.IsTree) (oS : {v // v ∈ S})
    (v₀ v : {v // v ∈ R}) (w₀ w : {v // v ∈ S})
    (h₀ : Γ.Adj v₀.1 w₀.1) (h : Γ.Adj v.1 w.1) : Γ.Walk oS.1 oS.1 :=
  regularBoundaryRoute h₀ h (regularRegionTreeWalk S TS hTS htreeS oS w₀)
    (regularRegionTreeWalk R TR hTR htreeR v₀ v)
    (regularRegionTreeWalk S TS hTS htreeS w oS)

/-- The holonomy of the actual two-tree route is the relative crossing
multiplier. Arbitrary native bond operators are permitted. Source: SCP10,
accessible complement cycles, lines 1935–1990. -/
theorem regularBoundaryTreeRoute_holonomy (R S : Finset V)
    (TR : SimpleGraph {v : V // v ∈ R}) (TS : SimpleGraph {v : V // v ∈ S})
    [DecidableRel TR.Adj] [DecidableRel TS.Adj]
    (hTR : TR ≤ Γ.induce (R : Set V)) (hTS : TS ≤ Γ.induce (S : Set V))
    (htreeR : TR.IsTree) (htreeS : TS.IsTree)
    (oR : {v // v ∈ R}) (oS : {v // v ∈ S}) (u : Edge Γ → G)
    (v₀ v : {v // v ∈ R}) (w₀ w : {v // v ∈ S})
    (h₀ : Γ.Adj v₀.1 w₀.1) (h : Γ.Adj v.1 w.1) :
    regularWalkHolonomy u
        (regularBoundaryTreeRoute R S TR TS hTR hTS htreeR htreeS oS v₀ v w₀ w h₀ h) =
      (((regularRegionTreeGauge S TS hTS htreeS oS u).1 w)⁻¹ *
        regularDirectedTransport u h * (regularRegionTreeGauge R TR hTR htreeR oR u).1 v) *
      (((regularRegionTreeGauge S TS hTS htreeS oS u).1 w₀)⁻¹ *
        regularDirectedTransport u h₀ *
          (regularRegionTreeGauge R TR hTR htreeR oR u).1 v₀)⁻¹ := by
  rw [regularBoundaryTreeRoute, regularBoundaryRoute_holonomy,
    regularRegionTreeWalk_holonomy S TS hTS htreeS oS u,
    regularRegionTreeWalk_holonomy R TR hTR htreeR oR u,
    regularRegionTreeWalk_holonomy S TS hTS htreeS oS u,
    regularRegionTreeGauge_root]
  group

variable [Fintype V]

/-- The actual composition of the two boundary transports, rereading each
crossing edge under the complement boundary numbering. Source: SCP10,
accessible complement coordinates, lines 1935–1990. -/
noncomputable def regularCombinedBoundaryTransport (R : Finset V)
    (kR : {v : V // v ∈ R} → G) (kS : {v : V // v ∈ Finset.univ \ R} → G)
    (u : Edge Γ → G) :
    ({e : Edge Γ // IsRegionBoundaryEdge R e} → G) ≃
      ({e : Edge Γ // IsRegionBoundaryEdge R e} → G) := by
  classical
  exact (regularRegionBoundaryTransport R kR u).symm.trans
    (((regionBoundaryEdgeComplEquiv (G := Γ) R).arrowCongr (Equiv.refl G)).trans
      ((regularRegionBoundaryTransport (Finset.univ \ R) kS u).trans
        ((regionBoundaryEdgeComplEquiv (G := Γ) R).symm.arrowCongr (Equiv.refl G))))

omit [Fintype G] in
/-- The composition of the two actual boundary maps is left multiplication
by its value on the identity configuration, separately on each crossing bond. -/
theorem regularCombinedBoundaryTransport_apply (R : Finset V)
    (kR : {v : V // v ∈ R} → G) (kS : {v : V // v ∈ Finset.univ \ R} → G)
    (u : Edge Γ → G) (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G)
    (f : {e : Edge Γ // IsRegionBoundaryEdge R e}) :
    regularCombinedBoundaryTransport R kR kS u θ f =
      regularCombinedBoundaryTransport R kR kS u 1 f * θ f := by
  classical
  simp [regularCombinedBoundaryTransport, regularRegionBoundaryTransport,
    Equiv.arrowCongr, Equiv.piCongrRight, mul_assoc]

omit [Fintype G] in
/-- At a crossing directed from the smaller region endpoint to the larger
complement endpoint, the combined multiplier is the gauged bond operator. -/
theorem regularCombinedBoundaryTransport_tail (R : Finset V)
    (kR : {v : V // v ∈ R} → G) (kS : {v : V // v ∈ Finset.univ \ R} → G)
    (u : Edge Γ → G) (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G)
    (f : Edge Γ) (ht : f.1.1 ∈ R) (hh : f.1.2 ∉ R) :
    regularCombinedBoundaryTransport R kR kS u θ ⟨f, Or.inl ⟨ht, hh⟩⟩ =
      (kS ⟨f.1.2, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hh⟩⟩)⁻¹ * u f *
        kR ⟨f.1.1, ht⟩ * θ ⟨f, Or.inl ⟨ht, hh⟩⟩ := by
  classical
  simp [regularCombinedBoundaryTransport, regularRegionBoundaryTransport,
    Equiv.arrowCongr, Equiv.piCongrRight, regionBoundaryEdgeComplEquiv, ht, mul_assoc]

omit [Fintype G] in
/-- At a crossing directed from the larger region endpoint to the smaller
complement endpoint, the original bond operator occurs with its inverse. -/
theorem regularCombinedBoundaryTransport_head (R : Finset V)
    (kR : {v : V // v ∈ R} → G) (kS : {v : V // v ∈ Finset.univ \ R} → G)
    (u : Edge Γ → G) (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G)
    (f : Edge Γ) (ht : f.1.1 ∉ R) (hh : f.1.2 ∈ R) :
    regularCombinedBoundaryTransport R kR kS u θ ⟨f, Or.inr ⟨ht, hh⟩⟩ =
      (kS ⟨f.1.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ht⟩⟩)⁻¹ * (u f)⁻¹ *
        kR ⟨f.1.2, hh⟩ * θ ⟨f, Or.inr ⟨ht, hh⟩⟩ := by
  classical
  simp [regularCombinedBoundaryTransport, regularRegionBoundaryTransport,
    Equiv.arrowCongr, Equiv.piCongrRight, regionBoundaryEdgeComplEquiv, ht, mul_assoc]

end TNLean.PEPS

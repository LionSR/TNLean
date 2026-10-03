/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularBoundaryRoute
import TNLean.PEPS.TorusWalkWinding

/-!
# Complement cycle words from actual torus winding data

The endpoints and direction of a crossing step are derived from membership in
the native region. Two rooted trees then give an actual closed route through
the region and its complement. For any supplied complementary root loops with
the same integer seam crossing numbers as those routes, evaluation of their
constructed cycle words equals the relative combined boundary transport for
every commuting closure pair. The loops and words are independent of that pair.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, proof of Theorem 6.9,
local source lines 1935–1990. No group-valued relative holonomy identity is
assumed, and no existence theorem for the complementary loops is asserted.

**Scope restriction (simple torus graph):** The torus statements use width and
height at least three. The complementary replacement loops are constructed
separately, in `TNLean.PEPS.TorusComplementPathReplacement`; see
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V] {Γ : SimpleGraph V}

/-- The region endpoint of a native crossing edge, selected by membership. -/
def regularBoundaryInsideVertex (R : Finset V)
    (f : {e : Edge Γ // IsRegionBoundaryEdge R e}) : {v : V // v ∈ R} :=
  if ht : f.1.1.1 ∈ R then ⟨f.1.1.1, ht⟩ else
    ⟨f.1.1.2, by
      rcases f.2 with h | h
      · exact False.elim (ht h.1)
      · exact h.2⟩

/-- The complementary endpoint of the same native crossing edge. -/
def regularBoundaryOutsideVertex (R : Finset V)
    (f : {e : Edge Γ // IsRegionBoundaryEdge R e}) : {v : V // v ∈ Finset.univ \ R} :=
  if ht : f.1.1.1 ∈ R then
    ⟨f.1.1.2, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
      rcases f.2 with h | h
      · exact h.2
      · exact False.elim (h.1 ht)⟩⟩
  else ⟨f.1.1.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ht⟩⟩

/-- The actual crossing step directed from the region to its complement.
Source: SCP10, complementary boundary transports, lines 1935–1990. -/
theorem regularBoundaryCrossingAdj (R : Finset V)
    (f : {e : Edge Γ // IsRegionBoundaryEdge R e}) :
    Γ.Adj (regularBoundaryInsideVertex R f).1 (regularBoundaryOutsideVertex R f).1 := by
  unfold regularBoundaryInsideVertex regularBoundaryOutsideVertex
  split_ifs with ht
  · exact f.1.2.2
  · exact f.1.2.2.symm

variable {G : Type*} [Group G]

/-- The combined actual boundary equivalences have the multiplier determined
by their genuine region and complementary endpoints. Source: SCP10,
proof of Theorem 6.9, lines 1935–1990. -/
theorem regularCombinedBoundaryTransport_insideOutside (R : Finset V)
    (kR : {v : V // v ∈ R} → G) (kS : {v : V // v ∈ Finset.univ \ R} → G)
    (u : Edge Γ → G) (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G)
    (f : {e : Edge Γ // IsRegionBoundaryEdge R e}) :
    regularCombinedBoundaryTransport R kR kS u θ f =
      (kS (regularBoundaryOutsideVertex R f))⁻¹ *
        regularDirectedTransport u (regularBoundaryCrossingAdj R f) *
          kR (regularBoundaryInsideVertex R f) * θ f := by
  by_cases ht : f.1.1.1 ∈ R
  · have hh : f.1.1.2 ∉ R := by
      rcases f.2 with h | h
      · exact h.2
      · exact False.elim (h.1 ht)
    have hstep : regularDirectedTransport u (regularBoundaryCrossingAdj R f) = u f.1 := by
      unfold regularDirectedTransport
      simp only [regularBoundaryInsideVertex, regularBoundaryOutsideVertex, dite_eq_left ht]
      rw [ite_eq_left f.1.2.1, Edge.ofAdj_of_lt _ f.1.2.1]
    rw [hstep]
    simpa only [regularBoundaryInsideVertex, regularBoundaryOutsideVertex, dite_eq_left ht] using
      regularCombinedBoundaryTransport_tail R kR kS u θ f.1 ht hh
  · have hh : f.1.1.2 ∈ R := by
      rcases f.2 with h | h
      · exact False.elim (ht h.1)
      · exact h.2
    have hstep : regularDirectedTransport u (regularBoundaryCrossingAdj R f) = (u f.1)⁻¹ := by
      unfold regularDirectedTransport
      simp only [regularBoundaryInsideVertex, regularBoundaryOutsideVertex, dite_eq_right ht]
      rw [ite_eq_right (not_lt.mpr f.1.2.1.le), Edge.ofAdj_of_gt _ f.1.2.1]
    rw [hstep]
    simpa only [regularBoundaryInsideVertex, regularBoundaryOutsideVertex, dite_eq_right ht] using
      regularCombinedBoundaryTransport_head R kR kS u θ f.1 ht hh

section Torus

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]

local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height

/-- The actual two-tree route associated with two native torus crossing edges.
Its endpoints and crossing directions are derived from region membership.
Source: SCP10, complementary boundary routes, lines 1935–1990. -/
noncomputable def torusBoundaryTreeRoute (R : Finset X)
    (TR : SimpleGraph {v : X // v ∈ R})
    (TS : SimpleGraph {v : X // v ∈ Finset.univ \ R})
    (hTR : TR ≤ (Γₜ).induce (R : Set X))
    (hTS : TS ≤ (Γₜ).induce ((Finset.univ \ R : Finset X) : Set X))
    (htreeR : TR.IsTree) (htreeS : TS.IsTree) (oS : {v : X // v ∈ Finset.univ \ R})
    (f₀ f : {e : Edge Γₜ // IsRegionBoundaryEdge R e}) : (Γₜ).Walk oS.1 oS.1 :=
  regularBoundaryTreeRoute R (Finset.univ \ R) TR TS hTR hTS htreeR htreeS oS
    (regularBoundaryInsideVertex R f₀) (regularBoundaryInsideVertex R f)
    (regularBoundaryOutsideVertex R f₀) (regularBoundaryOutsideVertex R f)
    (regularBoundaryCrossingAdj R f₀) (regularBoundaryCrossingAdj R f)

variable [Fintype G]

/-- The genuine crossing-edge route realizes the relative multiplier of the
actual region and complementary boundary equivalences. No endpoint relation or
holonomy identity is supplied. Source: SCP10, lines 1935–1990. -/
theorem torusBoundaryTreeRoute_holonomy (R : Finset X)
    (TR : SimpleGraph {v : X // v ∈ R})
    (TS : SimpleGraph {v : X // v ∈ Finset.univ \ R})
    [DecidableRel TR.Adj] [DecidableRel TS.Adj]
    (hTR : TR ≤ (Γₜ).induce (R : Set X))
    (hTS : TS ≤ (Γₜ).induce ((Finset.univ \ R : Finset X) : Set X))
    (htreeR : TR.IsTree) (htreeS : TS.IsTree)
    (oR : {v : X // v ∈ R}) (oS : {v : X // v ∈ Finset.univ \ R})
    (u : Edge Γₜ → G) (f₀ f : {e : Edge Γₜ // IsRegionBoundaryEdge R e}) :
    regularWalkHolonomy u (torusBoundaryTreeRoute R TR TS hTR hTS htreeR htreeS oS f₀ f) =
      regularCombinedBoundaryTransport R (regularRegionTreeGauge R TR hTR htreeR oR u).1
        (regularRegionTreeGauge (Finset.univ \ R) TS hTS htreeS oS u).1 u 1 f *
      (regularCombinedBoundaryTransport R (regularRegionTreeGauge R TR hTR htreeR oR u).1
        (regularRegionTreeGauge (Finset.univ \ R) TS hTS htreeS oS u).1 u 1 f₀)⁻¹ := by
  let kR := (regularRegionTreeGauge R TR hTR htreeR oR u).1
  let kS := (regularRegionTreeGauge (Finset.univ \ R) TS hTS htreeS oS u).1
  have hm (e : {e : Edge Γₜ // IsRegionBoundaryEdge R e}) :
      regularCombinedBoundaryTransport R kR kS u 1 e =
        (kS (regularBoundaryOutsideVertex R e))⁻¹ *
          regularDirectedTransport u (regularBoundaryCrossingAdj R e) *
            kR (regularBoundaryInsideVertex R e) := by
    simpa only [Pi.one_apply, mul_one] using
      regularCombinedBoundaryTransport_insideOutside R kR kS u 1 e
  rw [torusBoundaryTreeRoute, regularBoundaryTreeRoute_holonomy R (Finset.univ \ R)
    TR TS hTR hTS htreeR htreeS oR oS u]
  exact congrArg₂ (fun a b : G => a * b⁻¹) (hm f).symm (hm f₀).symm

/-- Fixed genuine complementary loops with the same torus winding as the
reference routes give the required relative cycle-word identities for every
commuting closure pair. The winding premise is entirely geometric; the walks
are chosen before the closure labels. Source: SCP10, lines 1935–1990. -/
theorem regularRegionCycleWord_eval_torusClosure_of_winding_eq (R : Finset X)
    (TR : SimpleGraph {v : X // v ∈ R})
    (TS : SimpleGraph {v : X // v ∈ Finset.univ \ R})
    [DecidableRel TR.Adj] [DecidableRel TS.Adj]
    (hTR : TR ≤ (Γₜ).induce (R : Set X))
    (hTS : TS ≤ (Γₜ).induce ((Finset.univ \ R : Finset X) : Set X))
    (htreeR : TR.IsTree) (htreeS : TS.IsTree)
    (oR : {v : X // v ∈ R}) (oS : {v : X // v ∈ Finset.univ \ R})
    (f₀ : {e : Edge Γₜ // IsRegionBoundaryEdge R e})
    (p : {e : Edge Γₜ // IsRegionBoundaryEdge R e} →
      ((Γₜ).induce ((Finset.univ \ R : Finset X) : Set X)).Walk oS oS)
    (hwind : ∀ f, torusWalkWinding
        ((p f).map (SimpleGraph.Embedding.induce
          ((Finset.univ \ R : Finset X) : Set X)).toHom) =
      torusWalkWinding (torusBoundaryTreeRoute R TR TS hTR hTS htreeR htreeS oS f₀ f))
    (g h : G) (hgh : Commute g h) :
    ∀ f, FreeGroup.lift
        (regularRegionTreeCycleResidual (Finset.univ \ R) TS hTS htreeS oS
          (torusClosureEdgeAssignment g h))
        (regularRegionCycleWord (Finset.univ \ R) TS (p f)) =
      regularCombinedBoundaryTransport R
        (regularRegionTreeGauge R TR hTR htreeR oR (torusClosureEdgeAssignment g h)).1
        (regularRegionTreeGauge (Finset.univ \ R) TS hTS htreeS oS
          (torusClosureEdgeAssignment g h)).1 (torusClosureEdgeAssignment g h) 1 f *
      (regularCombinedBoundaryTransport R
        (regularRegionTreeGauge R TR hTR htreeR oR (torusClosureEdgeAssignment g h)).1
        (regularRegionTreeGauge (Finset.univ \ R) TS hTS htreeS oS
          (torusClosureEdgeAssignment g h)).1 (torusClosureEdgeAssignment g h) 1 f₀)⁻¹ := by
  intro f
  rw [regularRegionCycleWord_eval_rootLoop, regularWalkHolonomy_inducedWalk,
    regularWalkHolonomy_torusClosure_eq_of_winding_eq g h hgh _ _ (hwind f)]
  exact torusBoundaryTreeRoute_holonomy R TR TS hTR hTS htreeR htreeS oR oS
    (torusClosureEdgeAssignment g h) f₀ f

end Torus

end TNLean.PEPS

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusIncidentCoordinates
import TNLean.PEPS.GraphOrientedAveragingBondState

/-!
# Native torus edge orientation

The source's incoming legs are top and left; outgoing legs are right and down.
Thus horizontal native arrows point right and vertical arrows point down.
The edge-flip flag records this convention independently of the total order
used to store the finite simple graph edges.

Source: SCP10, Definition 5.1, equation `eq:2d-ug-sym`.
-/

noncomputable section
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

/-- The tail of a native rightward/downward oriented torus bond. -/
def torusNativeEdgeTail (f : Edge (torusGraph width height)) : TorusVertex width height :=
  match torusEdgeEquiv.symm f with
  | Sum.inl v => v
  | Sum.inr v => (v.1, v.2 + 1)

/-- Reverse an ordered graph edge precisely when its first endpoint is not
the native rightward/downward tail. -/
def torusNativeEdgeFlip (f : Edge (torusGraph width height)) : Bool :=
  decide (f.1.1 ≠ torusNativeEdgeTail f)

/-- Rightward bonds have their left native vertex as tail, including seam bonds. -/
@[simp] theorem torusNativeEdgeTail_right (v : TorusVertex width height) :
    torusNativeEdgeTail (torusRightEdge v) = v := by
  unfold torusNativeEdgeTail
  rw [show torusEdgeEquiv.symm (torusRightEdge v) = Sum.inl v from
    torusEdgeEquiv.symm_apply_apply (Sum.inl v)]

/-- Vertical bonds point downward, including seam bonds. -/
@[simp] theorem torusNativeEdgeTail_up (v : TorusVertex width height) :
    torusNativeEdgeTail (torusUpEdge v) = (v.1, v.2 + 1) := by
  unfold torusNativeEdgeTail
  rw [show torusEdgeEquiv.symm (torusUpEdge v) = Sum.inr v from
    torusEdgeEquiv.symm_apply_apply (Sum.inr v)]

/-- Every declared native tail is one of the actual two edge endpoints. -/
theorem torusNativeEdgeTail_mem_endpoints (f : Edge (torusGraph width height)) :
    torusNativeEdgeTail f = f.1.1 ∨ torusNativeEdgeTail f = f.1.2 := by
  obtain ⟨z, rfl⟩ := torusEdgeEquiv.surjective f
  rcases z with v | v
  · change torusNativeEdgeTail (torusRightEdge v) = (torusRightEdge v).1.1 ∨
      torusNativeEdgeTail (torusRightEdge v) = (torusRightEdge v).1.2
    rw [torusNativeEdgeTail_right]
    rcases Edge.ofAdj_endpoints (torusGraph_adj_right v.1 v.2) with h | h
    · exact Or.inl h.1.symm
    · exact Or.inr h.2.symm
  · change torusNativeEdgeTail (torusUpEdge v) = (torusUpEdge v).1.1 ∨
      torusNativeEdgeTail (torusUpEdge v) = (torusUpEdge v).1.2
    rw [torusNativeEdgeTail_up]
    rcases Edge.ofAdj_endpoints (torusGraph_adj_up v.1 v.2) with h | h
    · exact Or.inr h.2.symm
    · exact Or.inl h.1.symm

/-- Ordinary simple-graph tori have four distinct incident bonds at every vertex. -/
theorem card_torusIncidentEdge (v : TorusVertex width height) :
    Fintype.card (IncidentEdge (torusGraph width height) v) = 4 := by
  simpa using (Fintype.card_congr (torusIncidentLegEquiv v)).symm

/-- The native tail occurs exactly at the right and down legs, numbered one and two. -/
theorem torusNativeEdgeTail_leg_iff (v : TorusVertex width height) (i : Fin 4) :
    torusNativeEdgeTail (torusIncidentLeg v i).1 = v ↔ i = 1 ∨ i = 2 := by
  have ht : (v.1, v.2 + 1) ≠ v := (torusGraph_adj_up v.1 v.2).ne.symm
  have hl : (v.1 - 1, v.2) ≠ v := by
    intro hv
    apply (torusGraph_adj_right (v.1 - 1) v.2).ne
    exact hv.trans (by simp)
  fin_cases i <;>
    simp [torusIncidentLeg, torusTopLeg, torusRightLeg, torusDownLeg, torusLeftLeg,
      torusDownEdge, torusLeftEdge, ht, hl]

/-- Incidence coordinates detect the native outgoing legs without assuming an
agreement between the torus arrows and the total vertex order. -/
theorem torusNativeEdgeTail_incident_iff (v : TorusVertex width height)
    (f : IncidentEdge (torusGraph width height) v) :
    torusNativeEdgeTail f.1 = v ↔
      (torusIncidentLegEquiv v).symm f = 1 ∨ (torusIncidentLegEquiv v).symm f = 2 := by
  obtain ⟨i, rfl⟩ := (torusIncidentLegEquiv v).surjective f
  simp only [Equiv.symm_apply_apply]
  exact torusNativeEdgeTail_leg_iff v i

/-- The graph edge-flip flag gives exactly the native tail predicate. -/
theorem graphNativeTail_torus_iff (v : TorusVertex width height)
    (f : IncidentEdge (torusGraph width height) v) :
    graphNativeTail torusNativeEdgeFlip v f ↔ torusNativeEdgeTail f.1 = v := by
  by_cases h : f.1.1.1 = torusNativeEdgeTail f.1
  · simp [graphNativeTail, torusNativeEdgeFlip, h]
  · have ht : torusNativeEdgeTail f.1 = f.1.1.2 :=
      (torusNativeEdgeTail_mem_endpoints f.1).resolve_left (Ne.symm h)
    simp [graphNativeTail, torusNativeEdgeFlip, ht, ne_of_lt f.1.2.1]

/-- The native outgoing legs are exactly right and down in four-leg coordinates. -/
theorem graphNativeTail_torus_leg_iff (v : TorusVertex width height) (i : Fin 4) :
    graphNativeTail torusNativeEdgeFlip v (torusIncidentLeg v i) ↔ i = 1 ∨ i = 2 := by
  rw [graphNativeTail_torus_iff, torusNativeEdgeTail_leg_iff]

end TNLean.PEPS

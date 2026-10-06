/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusFlatConnectionGauge

/-!
# Removing a flat connection away from any two native graph seams

The group-valued tree gauge may be based at any torus vertex. It removes all
bond labels except those crossing the selected horizontal and vertical seams.
These are the actual native graph edges, not a proposed boundary-space equality.
The simple-graph torus has both periods at least three.
-/

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height

/-- The actual graph edges crossing a selected column seam or row seam. -/
noncomputable def torusGraphSeamCut (c : ZMod width) (r : ZMod height) :
    Finset (Edge Γₜ) := by
  classical
  exact Finset.univ.filter fun e ↦
    ((torusEdgeEquiv (width := width) (height := height)).symm e).elim
      (fun v : X ↦ v.1 + 1 = c) (fun v : X ↦ v.2 + 1 = r)

/-- Horizontal bonds are cut exactly when they cross the selected column seam. -/
@[simp] theorem torusRightEdge_mem_graphSeamCut (c : ZMod width) (r : ZMod height) (v : X) :
    torusRightEdge v ∈ torusGraphSeamCut c r ↔ v.1 + 1 = c := by
  change torusEdgeEquiv (Sum.inl v) ∈ _ ↔ _
  simp [torusGraphSeamCut]

/-- Vertical bonds are cut exactly when they cross the selected row seam. -/
@[simp] theorem torusUpEdge_mem_graphSeamCut (c : ZMod width) (r : ZMod height) (v : X) :
    torusUpEdge v ∈ torusGraphSeamCut c r ↔ v.2 + 1 = r := by
  change torusEdgeEquiv (Sum.inr v) ∈ _ ↔ _
  simp [torusGraphSeamCut]

variable {G : Type*} [Group G]

omit [NeZero width] [NeZero height] [Fact (2 < width)] [Fact (2 < height)] in
/-- Translation preserves the flat square equations. -/
theorem IsTorusFlat.translate {a b : X → G} (hab : IsTorusFlat a b) (s : X) :
    IsTorusFlat (fun v ↦ a (v + s)) (fun v ↦ b (v + s)) := by
  intro v
  simpa only [Prod.add_def, add_assoc, add_left_comm, add_comm] using hab (v + s)

/-- At arbitrary seam positions a flat native graph connection has a vertex
gauge equal to the identity on every uncut edge. No holonomy is assumed trivial. -/
theorem exists_vertexGauge_off_torusGraphSeamCut (p : Edge Γₜ → G)
    (hp : IsTorusFlat (torusNativeRightTransport p) (torusNativeUpTransport p))
    (c : ZMod width) (r : ZMod height) :
    ∃ q : X → G, ∀ e : Edge Γₜ, e ∉ torusGraphSeamCut c r →
      q e.1.2 * p e * (q e.1.1)⁻¹ = 1 := by
  let a := torusNativeRightTransport p
  let b := torusNativeUpTransport p
  let s : X := (c, r)
  let a' : X → G := fun v ↦ a (v + s)
  let b' : X → G := fun v ↦ b (v + s)
  have hflat : IsTorusFlat a' b' := hp.translate s
  let k : X → G := fun v ↦ torusTreeGauge a' b' (v - s)
  have hr (v : X) (hv : v.1 + 1 ≠ c) :
      (k (v.1 + 1, v.2))⁻¹ * a v * k v = 1 := by
    have hh := hflat.torusTreeGauge_right (v - s)
    have hz : (v - s).1 + 1 ≠ 0 := by
      change v.1 - c + 1 ≠ 0
      intro h
      apply hv
      linear_combination h
    rw [ite_eq_right hz] at hh
    simpa only [k, a', s, Prod.sub_def, Prod.add_def, sub_add_cancel,
      sub_add_eq_add_sub] using hh
  have hu (v : X) (hv : v.2 + 1 ≠ r) :
      (k (v.1, v.2 + 1))⁻¹ * b v * k v = 1 := by
    have hh := hflat.torusTreeGauge_up (v - s)
    have hz : (v - s).2 + 1 ≠ 0 := by
      change v.2 - r + 1 ≠ 0
      intro h
      apply hv
      linear_combination h
    rw [ite_eq_right hz] at hh
    simpa only [k, b', s, Prod.sub_def, Prod.add_def, sub_add_cancel,
      sub_add_eq_add_sub] using hh
  refine ⟨fun v ↦ (k v)⁻¹, ?_⟩
  intro e he
  simp only [inv_inv]
  change regularVertexGaugeOperators k p e = 1
  obtain ⟨v | v, rfl⟩ := torusEdgeEquiv.surjective e
  · have hv := (mt (torusRightEdge_mem_graphSeamCut c r v).mpr he)
    have hg := (regularDirectedTransport_gauge p k (torusGraph_adj_right v.1 v.2)).trans (hr v hv)
    change (if v < (v.1 + 1, v.2) then regularVertexGaugeOperators k p (torusRightEdge v)
      else (regularVertexGaugeOperators k p (torusRightEdge v))⁻¹) = 1 at hg
    split_ifs at hg
    · exact hg
    · exact inv_eq_one.mp hg
  · have hv := (mt (torusUpEdge_mem_graphSeamCut c r v).mpr he)
    have hg := (regularDirectedTransport_gauge p k (torusGraph_adj_up v.1 v.2)).trans (hu v hv)
    change (if v < (v.1, v.2 + 1) then regularVertexGaugeOperators k p (torusUpEdge v)
      else (regularVertexGaugeOperators k p (torusUpEdge v))⁻¹) = 1 at hg
    split_ifs at hg
    · exact hg
    · exact inv_eq_one.mp hg

end TNLean.PEPS

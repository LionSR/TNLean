/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegionBlock.UnionInjectivityOverlap3b

/-!
# Transport and fused-leg utilities for overlapping region blocks

This file provides transport lemmas for physical configurations and blocked-region weights,
together with surjectivity of the physical leg fused from the blue and complement blocks of a
three-block geometry. These utilities support the live overlapping-union route and later region
transport constructions.
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
variable {A : Tensor G d}

/-! ### Transport of physical configurations, weights, and injectivity along region equality

The right-geometry rebuild produces a vanishing combination of the blocked weights of the
geometry-native host `univ \ red`, which is the literal region `R₂`. To feed the combination
to the left inverse for `R₂`, the weight is transported along the region-set equality
`univ \ red = R₂`, mirroring the boundary-configuration transport `regionBoundaryConfigCongr`.
-/

/-- The transport equivalence of physical configurations along a region-set equality: relabel
the vertex index along the equality of regions. -/
def regionPhysicalConfigCongr {S R : Finset V} (h : S = R) :
    RegionPhysicalConfig (V := V) (d := d) S ≃ RegionPhysicalConfig (V := V) (d := d) R :=
  Equiv.piCongrLeft' _ (Equiv.subtypeEquivRight (fun _ => by rw [h]))

omit [Fintype V] [DecidableEq V] [LinearOrder V] [DecidableRel G.Adj] in
/-- The transported physical configuration reads the same value as the original on a vertex. -/
theorem regionPhysicalConfigCongr_apply {S R : Finset V} (h : S = R)
    (τ : RegionPhysicalConfig (V := V) (d := d) S) (w : {w : V // w ∈ R}) :
    regionPhysicalConfigCongr (d := d) h τ w = τ ⟨w.1, by rw [h]; exact w.2⟩ := rfl

omit [DecidableEq V] in
/-- The blocked-region weight transports along a region-set equality: for equal regions the
weight of a configuration agrees with the weight of its transported boundary and physical
configurations. -/
theorem regionBlockedWeight_congr {S R : Finset V} (h : S = R)
    (bdry : RegionBoundaryConfig (G := G) A S)
    (τ : RegionPhysicalConfig (V := V) (d := d) S) :
    regionBlockedWeight (G := G) A S bdry τ =
      regionBlockedWeight (G := G) A R
        (regionBoundaryConfigCongr (A := A) h bdry)
        (regionPhysicalConfigCongr (d := d) h τ) := by
  subst h
  rfl

/-! ### Surjectivity of the fused complement physical leg

The fused leg `complPhysical σblue σcompl` ranges over every physical configuration of the host
`univ \ red` as the blue and complement legs vary: a host vertex lies in exactly one of the blue
and complement blocks (the red block is disjoint from the host), so reading the prescribed leg on
the blue block and on the complement block recovers it. -/

omit [LinearOrder V] in
/-- The fused complement physical leg is surjective: every physical configuration of the host
`univ \ g.red` is `g.complPhysical σblue σcompl` for some blue and complement legs. -/
theorem ThreeBlockGeometry.complPhysical_surjective (g : ThreeBlockGeometry V) :
    Function.Surjective
      (fun p : RegionPhysicalConfig (V := V) (d := d) g.blue ×
          RegionPhysicalConfig (V := V) (d := d) g.complement =>
        g.complPhysical (d := d) p.1 p.2) := by
  classical
  intro τ
  refine ⟨⟨fun w => τ ⟨w.1, ?_⟩, fun w => τ ⟨w.1, ?_⟩⟩, ?_⟩
  · -- A blue vertex lies in the host `univ \ red`.
    rw [Finset.mem_sdiff]
    exact ⟨Finset.mem_univ _, fun hr => (Finset.disjoint_left.mp g.red_disjoint_blue) hr w.2⟩
  · -- A complement vertex lies in the host `univ \ red`.
    rw [Finset.mem_sdiff]
    exact ⟨Finset.mem_univ _, fun hr => (Finset.disjoint_left.mp g.red_disjoint_complement) hr w.2⟩
  · funext w
    simp only
    by_cases hb : w.1 ∈ g.blue
    · rw [g.complPhysical_apply_blue _ _ w hb]
    · -- A host vertex outside the blue block lies in the complement block.
      have hwnotred : w.1 ∉ g.red := (Finset.mem_sdiff.mp w.2).2
      have hc : w.1 ∈ g.complement := by
        have hcover : w.1 ∈ g.red ∪ g.blue ∪ g.complement := by
          rw [g.cover_univ]; exact Finset.mem_univ _
        rcases Finset.mem_union.mp hcover with hrb | hc
        · rcases Finset.mem_union.mp hrb with hr | hbl
          · exact absurd hr hwnotred
          · exact absurd hbl hb
        · exact hc
      rw [g.complPhysical_apply_not_blue _ _ w hb hc]

end PEPS
end TNLean

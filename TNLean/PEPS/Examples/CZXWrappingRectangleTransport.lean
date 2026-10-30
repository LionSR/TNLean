/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.CZXOpenRegion
import TNLean.PEPS.CZXRectangleBoundary
import TNLean.PEPS.TorusWindowComplement

/-!
# Translation of actual CZX region contractions

Translations preserve the four directional legs, including their native bottom
and left pair reversal. Reindexing incident bonds therefore transports the actual
open-region contraction, without introducing exterior bond multiplicities.
The cyclic coordinate rectangle is the existing `torusArcRectangle`.

**Scope restriction:** both torus periods are at least three. The rectangle
results require positive side lengths strictly below their periods; full-width
cylinders have a different boundary. See
`docs/paper-gaps/rmp_peps_czx_boundary_chain.tex`.

**Local fix (bond orientation):** bottom and left pairs retain the reversal of
`docs/paper-gaps/rmp_peps_czx_bond_orientation.tex`.

Source: arXiv:2011.12127, Appendix A, lines 2502–2518 and 2582–2605.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

/-- A cyclic coordinate rectangle is the translate of the bounded origin
rectangle, including translations through either coordinate seam. -/
theorem czxWrappingRectangle_eq_map (s : TorusVertex width height)
    (w h : ℕ) (hw : 0 < w) (hh : 0 < h) (hwp : w < width) (hhp : h < height) :
    torusArcRectangle s w h =
      Region.map (translate s.1 s.2) (torusContiguousRectangle 0 0 w h) := by
  rw [← torusArcRectangle_eq_torusContiguousRectangle 0 0 w h hw hh
    (by omega) (by omega)]
  ext v
  simp [mem_torusArcRectangle, translate, translateEquiv]

/-- Translation of the actual native crossing-bond labels. -/
noncomputable def czxWrappingRectangleBoundaryTransport (a : ZMod width) (b : ZMod height)
    (R : Finset (TorusVertex width height)) :
    RegionBoundaryConfig (czxPEPS width height) R ≃
      RegionBoundaryConfig (czxPEPS width height) (Region.map (translate a b) R) :=
  Equiv.arrowCongr (regionBoundaryEdgeMapEquiv (translate a b) R).symm (Equiv.refl (Fin 4))

private theorem incident_translate (a : ZMod width) (b : ZMod height)
    (R : Finset (TorusVertex width height)) (e : Edge (torusGraph width height)) :
    IsRegionIncidentEdge (Region.map (translate a b) R) (Edge.map (translate a b) e) ↔
      IsRegionIncidentEdge R e := by
  unfold IsRegionIncidentEdge
  rcases Edge.map_endpoints (translate a b) e with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [h₁, h₂, mem_Region_map_apply, mem_Region_map_apply]
  · rw [h₁, h₂, mem_Region_map_apply, mem_Region_map_apply]
    exact or_comm

/-- All bonds touching a translated region are precisely the translates of
the original incident bonds. -/
noncomputable def czxWrappingRectangleIncidentEdgeEquiv (a : ZMod width) (b : ZMod height)
    (R : Finset (TorusVertex width height)) :
    {e : Edge (torusGraph width height) // IsRegionIncidentEdge R e} ≃
      {e : Edge (torusGraph width height) //
        IsRegionIncidentEdge (Region.map (translate a b) R) e} :=
  (Edge.equiv (translate a b)).subtypeEquiv fun e => (incident_translate a b R e).symm

/-- Reindex the incident labels, summing exactly the same internal bonds. -/
noncomputable def czxWrappingRectangleIncidentTransport (a : ZMod width) (b : ZMod height)
    (R : Finset (TorusVertex width height)) :
    RegionIncidentConfig (czxPEPS width height) R ≃
      RegionIncidentConfig (czxPEPS width height) (Region.map (translate a b) R) :=
  Equiv.arrowCongr (czxWrappingRectangleIncidentEdgeEquiv a b R) (Equiv.refl (Fin 4))

private theorem map_up (a : ZMod width) (b : ZMod height) (v : TorusVertex width height) :
    Edge.map (translate a b) (torusUpEdge v) = torusUpEdge (translate a b v) :=
  translateEdge_torusUpEdge a b v

private theorem map_right (a : ZMod width) (b : ZMod height) (v : TorusVertex width height) :
    Edge.map (translate a b) (torusRightEdge v) = torusRightEdge (translate a b v) :=
  translateEdge_torusRightEdge a b v

private theorem map_down (a : ZMod width) (b : ZMod height) (v : TorusVertex width height) :
    Edge.map (translate a b) (torusDownEdge v) = torusDownEdge (translate a b v) := by
  simp only [torusDownEdge, map_up, translate_apply]
  congr 2
  ring

private theorem map_left (a : ZMod width) (b : ZMod height) (v : TorusVertex width height) :
    Edge.map (translate a b) (torusLeftEdge v) = torusLeftEdge (translate a b v) := by
  simp only [torusLeftEdge, map_right, translate_apply]
  congr 2
  ring

/-- Translation preserves the actual CZX component, with the corrected
directional bond convention. -/
theorem czxWrappingRectangle_component_translate (a : ZMod width) (b : ZMod height)
    (v : TorusVertex width height) (ζ : Edge (torusGraph width height) → Fin 4) (p : Fin 16) :
    (czxPEPS width height).component (translate a b v)
        (fun e => ζ (Edge.map (translate a b).symm e.1)) p =
      (czxPEPS width height).component v (fun e => ζ e.1) p := by
  change czxSiteTensor (ζ (Edge.map (translate a b).symm (torusUpEdge (translate a b v))))
    (ζ (Edge.map (translate a b).symm (torusRightEdge (translate a b v))))
    (czxBondSwap (ζ (Edge.map (translate a b).symm (torusDownEdge (translate a b v)))))
    (czxBondSwap (ζ (Edge.map (translate a b).symm (torusLeftEdge (translate a b v))))) p = _
  rw [← map_up, ← map_right, ← map_down, ← map_left]
  simp only [Edge.map_symm_map]
  rfl

private theorem boundaryLabel_translate (a : ZMod width) (b : ZMod height)
    (R : Finset (TorusVertex width height)) (η : RegionIncidentConfig (czxPEPS width height) R) :
    regionIncidentBoundaryLabel (czxPEPS width height) (Region.map (translate a b) R)
        (czxWrappingRectangleIncidentTransport a b R η) =
      czxWrappingRectangleBoundaryTransport a b R
        (regionIncidentBoundaryLabel (czxPEPS width height) R η) := by
  rfl

private theorem incidentWeight_translate (a : ZMod width) (b : ZMod height)
    (R : Finset (TorusVertex width height)) (η : RegionIncidentConfig (czxPEPS width height) R)
    (σ : RegionPhysicalConfig (d := 16) R) :
    regionIncidentWeight (czxPEPS width height) (Region.map (translate a b) R)
        (czxWrappingRectangleIncidentTransport a b R η)
        (regionPhysicalConfigMapEquiv (d := 16) (translate a b) R σ) =
      regionIncidentWeight (czxPEPS width height) R η σ := by
  classical
  change ({e : Edge (torusGraph width height) // IsRegionIncidentEdge R e} → Fin 4) at η
  let θ : {e : Edge (torusGraph width height) //
      IsRegionIncidentEdge (Region.map (translate a b) R) e} → Fin 4 :=
    fun e => η ((czxWrappingRectangleIncidentEdgeEquiv a b R).symm e)
  let ζ : Edge (torusGraph width height) → Fin 4 :=
    fun e => if he : IsRegionIncidentEdge R e then η ⟨e, he⟩ else 0
  unfold regionIncidentWeight
  symm
  refine Fintype.prod_equiv (Finset.equivMap (translate a b).toEquiv.toEmbedding R) _ _ ?_
  intro v
  let v' : {u // u ∈ Region.map (translate a b) R} :=
    ⟨translate a b v.1, (mem_Region_map_apply (translate a b) R v.1).mpr v.2⟩
  have hl (e : IncidentEdge (torusGraph width height) v.1) :
      ζ e.1 = η ⟨e.1, isRegionIncidentEdge_of_regionVertex R v e⟩ := by
    simp [ζ, isRegionIncidentEdge_of_regionVertex R v e]
  have hr (e : IncidentEdge (torusGraph width height) v'.1) :
      θ ⟨e.1, isRegionIncidentEdge_of_regionVertex _ v' e⟩ =
        ζ (Edge.map (translate a b).symm e.1) := by
    have he := ((czxWrappingRectangleIncidentEdgeEquiv a b R).symm
      ⟨e.1, isRegionIncidentEdge_of_regionVertex _ v' e⟩).2
    change IsRegionIncidentEdge R (Edge.map (translate a b).symm e.1) at he
    change η ⟨Edge.map (translate a b).symm e.1, he⟩ =
      (if he' : IsRegionIncidentEdge R (Edge.map (translate a b).symm e.1) then
        η ⟨Edge.map (translate a b).symm e.1, he'⟩ else 0)
    rw [dite_eq_left he]
  have hp : regionPhysicalConfigMapEquiv (d := 16) (translate a b) R σ
      ((Finset.equivMap (translate a b).toEquiv.toEmbedding R) v) = σ v := by
    change σ ((Finset.equivMap (translate a b).toEquiv.toEmbedding R).symm
      ((Finset.equivMap (translate a b).toEquiv.toEmbedding R) v)) = σ v
    rw [Equiv.symm_apply_apply]
  change (czxPEPS width height).component v.1
      (fun e => η ⟨e.1, isRegionIncidentEdge_of_regionVertex R v e⟩) (σ v) =
    (czxPEPS width height).component v'.1
      (fun e => θ ⟨e.1, isRegionIncidentEdge_of_regionVertex _ v' e⟩) _
  rw [hp]
  dsimp only [czxPEPS, torusSiteTensor]
  rw [hr (torusTopLeg v'.1), hr (torusRightLeg v'.1),
    hr (torusDownLeg v'.1), hr (torusLeftLeg v'.1)]
  simp only [← hl]
  exact (czxWrappingRectangle_component_translate a b v.1 ζ (σ v)).symm

/-- Equality of actual open-region contractions under torus translation.
Only incident labels are reindexed; no exterior multiplicity is assumed or
discarded. Source: review Appendix A, lines 2502–2518. -/
theorem openRegionWeight_czxWrappingRectangle_translate (a : ZMod width) (b : ZMod height)
    (R : Finset (TorusVertex width height))
    (μ : RegionBoundaryConfig (czxPEPS width height) R)
    (σ : RegionPhysicalConfig (d := 16) R) :
    openRegionWeight (czxPEPS width height) (Region.map (translate a b) R)
        (czxWrappingRectangleBoundaryTransport a b R μ)
        (regionPhysicalConfigMapEquiv (d := 16) (translate a b) R σ) =
      openRegionWeight (czxPEPS width height) R μ σ := by
  classical
  unfold openRegionWeight
  rw [← (czxWrappingRectangleIncidentTransport a b R).sum_comp]
  apply Finset.sum_congr rfl
  intro η _
  simp only [boundaryLabel_translate,
    (czxWrappingRectangleBoundaryTransport a b R).injective.eq_iff,
    incidentWeight_translate]

/-- Translating the plaquette bits translates their actual native bond
labels. This uses directional bonds, independent of stored endpoint order. -/
theorem czxWrappingRectangle_plaquetteBond_translate (a : ZMod width) (b : ZMod height)
    (q : TorusVertex width height → Fin 2) (e : Edge (torusGraph width height)) :
    czxPlaquetteBondConfig (fun v => q ((translate a b).symm v))
        (Edge.map (translate a b) e) = czxPlaquetteBondConfig q e := by
  obtain ⟨v | v, rfl⟩ := torusEdgeEquiv.surjective e
  · change czxPlaquetteBondConfig _ (Edge.map (translate a b) (torusRightEdge v)) =
      czxPlaquetteBondConfig q (torusRightEdge v)
    rw [map_right, czxPlaquetteBondConfig_right, czxPlaquetteBondConfig_right]
    change czxBond (q (v.1 + a + 1 - a, v.2 + b + 1 - b),
      q (v.1 + a + 1 - a, v.2 + b - b)) = _
    apply congrArg czxBond
    apply Prod.ext <;> apply congrArg q <;> apply Prod.ext <;> ring
  · change czxPlaquetteBondConfig _ (Edge.map (translate a b) (torusUpEdge v)) =
      czxPlaquetteBondConfig q (torusUpEdge v)
    rw [map_up, czxPlaquetteBondConfig_up, czxPlaquetteBondConfig_up]
    change czxBond (q (v.1 + a - a, v.2 + b + 1 - b),
      q (v.1 + a + 1 - a, v.2 + b + 1 - b)) = _
    apply congrArg czxBond
    apply Prod.ext <;> apply congrArg q <;> apply Prod.ext <;> ring

end TNLean.PEPS

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.NativeTorusClosures
import TNLean.PEPS.ParentHamiltonian.GraphDependentRegionSupport
import TNLean.PEPS.TorusGraphSeamGauge
import TNLean.PEPS.TorusPlaquetteFluxMeasurement

/-!
# Native commuting closures satisfy the actual plaquette parents

With independently sized bonds and independently chosen edge representations,
local virtual invariance moves commuting closures away from any selected
plaquette. The resulting internal matrices are identities, so the actual
open-region map supplies its boundary witness. No semi-regularity or local
injectivity is needed for this inclusion.

Source: SCP10, Theorem 5.7 and equation `eq:2d:move-strings`.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS

namespace DependentBondNetwork
variable {Vertex Edge : Type*} [Fintype Vertex] [Fintype Edge]
variable [DecidableEq Vertex] [DecidableEq Edge]
variable (tail head : Edge → Vertex) (D : Edge → Type*)
variable [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]
variable {G : Type*} [Group G] [Finite G] {Phys : Vertex → Type*}

/-- Local invariant tensors identify vertex-gauge-related inserted networks,
with each edge's own representation and each site's own physical alphabet.
Source: SCP10, Definition 5.1(i) and equation `eq:2d:move-strings`. -/
theorem network_vertexGauge_of_invariant
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (hA : ∀ v g, localSiteMap tail head D A v ∘ₗ
      incidentRepresentation tail head D U v g = localSiteMap tail head D A v)
    (p : Edge → G) (q : Vertex → G) :
    network tail head D A (fun e ↦ U e (q (head e) * p e * (q (tail e))⁻¹)) =
      network tail head D A (fun e ↦ U e (p e)) := by
  let _ := Fintype.ofFinite G
  let F := fun v ↦ LinearMap.toMatrix' (localSiteMap tail head D A v)
  have hrec : physicalMapSite tail head D F (averagingSite tail head D U) = A :=
    physicalMap_recover_representationAveragingSite tail head D _ A hA
  rw [← hrec, ← physicalMap_network, ← physicalMap_network]
  apply congrArg (dependentPhysicalProductFamilyMap F)
  funext σ
  exact network_averagingSite_vertexGauge tail head D U p q σ

end DependentBondNetwork

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "TV" => TorusVertex width height
local notation "TG" => torusGraph width height

private theorem zmod_add_two_ne {n : ℕ} [NeZero n] [Fact (2 < n)] (x : ZMod n) :
    x + 2 ≠ x ∧ x + 2 ≠ x + 1 := by
  have hn : 2 < n := Fact.out
  have htwo : (2 : ZMod n) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 2 n).mp h
    have := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  have hone : (1 : ZMod n) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 1 n).mp (by simp at h)
    have := Nat.le_of_dvd (by decide : 0 < 1) hd
    omega
  constructor
  · simpa using htwo
  · intro h
    have hh : (2 : ZMod n) = 1 := add_left_cancel h
    apply hone
    linear_combination hh

private theorem torusPlaquetteRegion_fst (v p : TV) (hp : p ∈ torusPlaquetteRegion v) :
    p.1 = v.1 ∨ p.1 = v.1 + 1 := by
  simp only [torusPlaquetteRegion, torusPlaquetteWalk, SimpleGraph.Walk.support,
    List.toFinset_cons, List.toFinset_nil, Finset.mem_insert, Finset.notMem_empty, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp

private theorem torusPlaquetteRegion_snd (v p : TV) (hp : p ∈ torusPlaquetteRegion v) :
    p.2 = v.2 ∨ p.2 = v.2 + 1 := by
  simp only [torusPlaquetteRegion, torusPlaquetteWalk, SimpleGraph.Walk.support,
    List.toFinset_cons, List.toFinset_nil, Finset.mem_insert, Finset.notMem_empty, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp

/-- Two seams placed two steps past a plaquette avoid all its internal edges,
including when either torus period is three. Source: SCP10, Theorem 5.7. -/
theorem torusPlaquette_internal_not_mem_shiftedGraphSeamCut
    (v : TV) (e : Edge TG)
    (ht : e.1.1 ∈ torusPlaquetteRegion v) (hh : e.1.2 ∈ torusPlaquetteRegion v) :
    e ∉ torusGraphSeamCut (v.1 + 2) (v.2 + 2) := by
  obtain ⟨p, rfl⟩ := torusEdgeEquiv.surjective e
  rcases p with p | p
  · change (torusRightEdge p).1.1 ∈ torusPlaquetteRegion v at ht
    change (torusRightEdge p).1.2 ∈ torusPlaquetteRegion v at hh
    have hp : (p.1 + 1, p.2) ∈ torusPlaquetteRegion v := by
      rcases Edge.ofAdj_endpoints (torusGraph_adj_right p.1 p.2) with ht' | hh'
      · simpa only [torusRightEdge, ht'.2] using hh
      · simpa only [torusRightEdge, hh'.1] using ht
    change torusRightEdge p ∉ torusGraphSeamCut (v.1 + 2) (v.2 + 2)
    rw [torusRightEdge_mem_graphSeamCut]
    intro he
    rcases torusPlaquetteRegion_fst v _ hp with hx | hx
    · exact (zmod_add_two_ne v.1).1 (he.symm.trans hx)
    · exact (zmod_add_two_ne v.1).2 (he.symm.trans hx)
  · change (torusUpEdge p).1.1 ∈ torusPlaquetteRegion v at ht
    change (torusUpEdge p).1.2 ∈ torusPlaquetteRegion v at hh
    have hp : (p.1, p.2 + 1) ∈ torusPlaquetteRegion v := by
      rcases Edge.ofAdj_endpoints (torusGraph_adj_up p.1 p.2) with ht' | hh'
      · simpa only [torusUpEdge, ht'.2] using hh
      · simpa only [torusUpEdge, hh'.1] using ht
    change torusUpEdge p ∉ torusGraphSeamCut (v.1 + 2) (v.2 + 2)
    rw [torusUpEdge_mem_graphSeamCut]
    intro he
    rcases torusPlaquetteRegion_snd v _ hp with hy | hy
    · exact (zmod_add_two_ne v.2).1 (he.symm.trans hy)
    · exact (zmod_add_two_ne v.2).2 (he.symm.trans hy)

variable {G : Type*} [Group G]

/-- Commuting native closure seams form a flat ordered graph connection.
Source: SCP10, Theorem 5.7, compatibility of the two closure strings. -/
theorem isTorusFlat_nativeClosure (g h : G) (hgh : Commute g h) :
    IsTorusFlat (torusNativeRightTransport (width := width) (height := height)
      (torusClosureEdgeAssignment g h))
      (torusNativeUpTransport (torusClosureEdgeAssignment g h)) := by
  intro v
  simp only [torusNativeRightTransport_closure, torusNativeUpTransport_closure]
  split_ifs <;> simp_all [hgh.inv_left.eq]

variable [Finite G] {d : ℕ}
open DependentBondNetwork

/-- Each slice of an actual commuting closure lies in the original plaquette
range, for arbitrary bond dimensions and local invariant tensors.
Source: SCP10, the local inclusion in Theorem 5.7. -/
theorem nativeClosure_slice_mem_torusPlaquetteGroundSpace
    (A : Tensor TG d)
    (U : (e : Edge TG) → G →* Matrix (graphBondAlphabet A e) (graphBondAlphabet A e) ℂ)
    (hA : ∀ v g, localSiteMap graphEdgeTail graphEdgeHead (graphBondAlphabet A)
      (graphDependentTensor A) v ∘ₗ
        incidentRepresentation graphEdgeTail graphEdgeHead (graphBondAlphabet A) U v g =
          localSiteMap graphEdgeTail graphEdgeHead (graphBondAlphabet A)
            (graphDependentTensor A) v)
    (g h : G) (hgh : Commute g h) (v : TV)
    (τ : RegionPhysicalConfig (d := d) (Finset.univ \ torusPlaquetteRegion v)) :
    (fun σ ↦ NativeTorus.closure (graphBondAlphabet A) U (graphDependentTensor A) g h
      (assembleRegionσ (torusPlaquetteRegion v) σ τ)) ∈
        regionGroundSpace A (torusPlaquetteRegion v) := by
  obtain ⟨q, hq⟩ := exists_vertexGauge_off_torusGraphSeamCut
    (torusClosureEdgeAssignment g h) (isTorusFlat_nativeClosure g h hgh) (v.1 + 2) (v.2 + 2)
  unfold NativeTorus.closure
  rw [← network_vertexGauge_of_invariant graphEdgeTail graphEdgeHead (graphBondAlphabet A)
    U (graphDependentTensor A) hA (torusClosureEdgeAssignment g h) q]
  apply graphDependentNetwork_slice_mem_regionGroundSpace_of_internal_eq_one
  intro e ht hh
  rw [show q (graphEdgeHead e) * torusClosureEdgeAssignment g h e *
      (q (graphEdgeTail e))⁻¹ = 1 from hq e
    (torusPlaquette_internal_not_mem_shiftedGraphSeamCut v e ht hh), map_one]

/-- Local invariance alone makes every commuting native closure satisfy all
actual plaquette parent constraints. Source: SCP10, Theorem 5.7. -/
theorem nativeClosure_mem_torusPlaquetteParentGroundSpace
    (A : Tensor TG d)
    (U : (e : Edge TG) → G →* Matrix (graphBondAlphabet A e) (graphBondAlphabet A e) ℂ)
    (hA : ∀ v g, localSiteMap graphEdgeTail graphEdgeHead (graphBondAlphabet A)
      (graphDependentTensor A) v ∘ₗ
        incidentRepresentation graphEdgeTail graphEdgeHead (graphBondAlphabet A) U v g =
          localSiteMap graphEdgeTail graphEdgeHead (graphBondAlphabet A)
            (graphDependentTensor A) v)
    (g h : G) (hgh : Commute g h) :
    NativeTorus.closure (graphBondAlphabet A) U (graphDependentTensor A) g h ∈
      regionParentGroundSpace A torusPlaquetteRegion := by
  simp only [regionParentGroundSpace, Submodule.mem_iInf, Submodule.mem_comap]
  intro v τ
  exact nativeClosure_slice_mem_torusPlaquetteGroundSpace A U hA g h hgh v τ

/-- The actual native commuting-closure span is contained in the original
plaquette parent space, without semi-regularity or local injectivity.
Source: SCP10, the inclusion in Theorem 5.7. -/
theorem nativeCommutingClosureSpan_le_torusPlaquetteParentGroundSpace
    (A : Tensor TG d)
    (U : (e : Edge TG) → G →* Matrix (graphBondAlphabet A e) (graphBondAlphabet A e) ℂ)
    (hA : ∀ v g, localSiteMap graphEdgeTail graphEdgeHead (graphBondAlphabet A)
      (graphDependentTensor A) v ∘ₗ
        incidentRepresentation graphEdgeTail graphEdgeHead (graphBondAlphabet A) U v g =
          localSiteMap graphEdgeTail graphEdgeHead (graphBondAlphabet A)
            (graphDependentTensor A) v) :
    NativeTorus.commutingClosureSpan (graphBondAlphabet A) U (graphDependentTensor A) ≤
      regionParentGroundSpace A torusPlaquetteRegion := by
  apply Submodule.span_le.mpr
  rintro _ ⟨p, rfl⟩
  exact nativeClosure_mem_torusPlaquetteParentGroundSpace A U hA p.1.1 p.1.2 p.2

end TNLean.PEPS

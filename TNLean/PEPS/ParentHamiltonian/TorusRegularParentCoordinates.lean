/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegularGlobalParentCoordinates
import TNLean.PEPS.TorusPlaquetteFluxMeasurement
import TNLean.PEPS.TorusIncidentGInjectivity

/-!
# Regular inverse coordinates of the native torus parent kernel

For periods at least three, the native four-site plaquettes cover every vertex
and both endpoints of every edge. A physical vector annihilated by all their
parent terms therefore has exact regular inverse coordinates. These coordinates
are invariant under independent vertex-left and shared-edge-right translations,
and vanish unless every native plaquette has identity quotient holonomy.

The local inverse coefficients are obtained from regular G-injectivity. None
of the three coordinate properties is imposed as a hypothesis on the vector.
This is the regular-representation part of the converse parent-ground-space
argument in SCP10, arXiv:1001.3807, Theorems 5.5 and 5.7. The general semi-regular
representation is not asserted here.

**Scope restriction (regular native torus):** The virtual representation is regular
and both periods are at least three. The semi-regular parent-kernel and
smaller-period statements remain separate; see
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height

/-- Every site belongs to the native plaquette based there. -/
theorem mem_torusPlaquetteRegion_self (v : X) : v ∈ torusPlaquetteRegion v :=
  List.mem_toFinset.mpr (torusPlaquetteWalk v).start_mem_support

/-- The native plaquette collection contains both endpoints of every edge. -/
theorem exists_torusPlaquetteRegion_contains_edge (e : Edge Γₜ) :
    ∃ v : X, e.1.1 ∈ torusPlaquetteRegion v ∧ e.1.2 ∈ torusPlaquetteRegion v := by
  obtain ⟨z, rfl⟩ := torusEdgeEquiv.surjective e
  rcases z with v | v
  · refine ⟨v, ?_⟩
    change (Edge.ofAdj (torusGraph_adj_right v.1 v.2)).1.1 ∈ _ ∧
      (Edge.ofAdj (torusGraph_adj_right v.1 v.2)).1.2 ∈ _
    rcases Edge.ofAdj_endpoints (torusGraph_adj_right v.1 v.2) with
      ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
      simp [h₁, h₂, torusPlaquetteRegion, torusPlaquetteWalk, SimpleGraph.Walk.support]
  · refine ⟨v, ?_⟩
    change (Edge.ofAdj (torusGraph_adj_up v.1 v.2)).1.1 ∈ _ ∧
      (Edge.ofAdj (torusGraph_adj_up v.1 v.2)).1.2 ∈ _
    rcases Edge.ofAdj_endpoints (torusGraph_adj_up v.1 v.2) with
      ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
      simp [h₁, h₂, torusPlaquetteRegion, torusPlaquetteWalk, SimpleGraph.Walk.support]

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}

/-- A nonflat native plaquette quotient is outside the support of the exposed
coordinates of any physical vector killed by that plaquette's parent term. -/
theorem globalDependentPhysicalMap_regularInverse_eq_zero_of_torusPlaquetteHolonomy
    (a : (v : X) → (IncidentEdge Γₜ v → G) → Fin d → ℂ)
    (F : (v : X) → Matrix (IncidentEdge Γₜ v → G) (Fin d) ℂ)
    (hF : ∀ v α η, (∑ s : Fin d, F v α s * a v η s) =
      regularLegProjector (IncidentEdge Γₜ v) α η)
    (v : X)
    (P : Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
      (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ)
    (hP : IsRegionParentInteraction (groupBondTensor a) (torusPlaquetteRegion v) P)
    (Ψ : (X → Fin d) → ℂ)
    (hΨ : regionLocalTerm (torusPlaquetteRegion v) P *ᵥ Ψ = 0)
    (α : RegularHalfEdgeConfig Γₜ G)
    (hhol : regularWalkHolonomy (regularHalfEdgeOperators α) (torusPlaquetteWalk v) ≠ 1) :
    globalDependentPhysicalMap F Ψ (fun w => α w.1) = 0 := by
  classical
  let R := torusPlaquetteRegion v
  have hsupport : ∀ x ∈ (torusPlaquetteWalk v).support, x ∈ (R : Set X) := by
    intro x hx
    exact List.mem_toFinset.mpr hx
  have hR : ((Γₜ).induce (R : Set X)).Connected := by
    have heq : (R : Set X) = {x | x ∈ (torusPlaquetteWalk v).support} := by
      ext x
      simp [R, torusPlaquetteRegion]
    rw [heq]
    exact (torusPlaquetteWalk v).connected_induce_support
  let o : {x : X // x ∈ R} := ⟨v, mem_torusPlaquetteRegion_self v⟩
  let p : ((Γₜ).induce (R : Set X)).Walk o o :=
    (torusPlaquetteWalk v).induce (R : Set X) hsupport
  apply globalDependentPhysicalMap_regularInverse_eq_zero_of_holonomy_ne_one
    a F hF R hR o p P hP Ψ hΨ α
  dsimp only [p]
  rw [regularWalkHolonomy_inducedWalk, SimpleGraph.Walk.map_induce]
  exact hhol

/-- Every vector in the actual native torus parent kernel admits reconstructing
regular coordinates with vertex-left invariance, shared-edge-right invariance,
and support on flat plaquette quotients. The coefficients are supplied by
regular G-injectivity, not by an assumed closure decomposition.
Source: SCP10, Theorems 5.5 and 5.7, restricted to the regular representation. -/
theorem IsGInjective.exists_torusParentCoordinates
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGInjective (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (P : (v : X) → Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
      (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ)
    (hP : ∀ v, IsRegionParentInteraction (groupBondTensor (torusIncidentSite a))
      (torusPlaquetteRegion v) (P v))
    (Ψ : (X → Fin d) → ℂ)
    (hΨ : ∀ v, regionLocalTerm (torusPlaquetteRegion v) (P v) *ᵥ Ψ = 0) :
    ∃ F : (v : X) → Matrix (IncidentEdge Γₜ v → G) (Fin d) ℂ,
      (∀ v α η, (∑ s : Fin d, F v α s * torusIncidentSite a v η s) =
        regularLegProjector (IncidentEdge Γₜ v) α η) ∧
      globalRegularTensorMap (torusIncidentSite a) (globalDependentPhysicalMap F Ψ) = Ψ ∧
      (∀ k α, globalDependentPhysicalMap F Ψ
          (fun w => regularHalfEdgeLeftMul k α w.1) =
        globalDependentPhysicalMap F Ψ (fun w => α w.1)) ∧
      (∀ r α, globalDependentPhysicalMap F Ψ
          (fun w => regularHalfEdgeRightMul r α w.1) =
        globalDependentPhysicalMap F Ψ (fun w => α w.1)) ∧
      (∀ α, (¬ ∀ v : X, regularWalkHolonomy (regularHalfEdgeOperators α)
          (torusPlaquetteWalk v) = 1) →
        globalDependentPhysicalMap F Ψ (fun w => α w.1) = 0) := by
  classical
  have hsite := fun v : X => ha.isGInjective_torusIncidentSite v
  choose F hF using fun v : X => (hsite v).exists_regularProjectorCoefficients
  have hparent : Ψ ∈ regionParentGroundSpace
      (groupBondTensor (torusIncidentSite a)) torusPlaquetteRegion := by
    rw [mem_regionParentGroundSpace_iff]
    intro v τ
    exact (regionLocalTerm_mulVec_eq_zero_iff _ _ (hP v) Ψ).mp (hΨ v) τ
  have hcover : ∀ v : X, ∃ w, v ∈ torusPlaquetteRegion w :=
    fun v => ⟨v, mem_torusPlaquetteRegion_self v⟩
  refine ⟨F, hF,
    globalRegularTensorMap_inverse_eq_self_of_mem_parent
      _ hsite F hF torusPlaquetteRegion hcover hparent, ?_, ?_, ?_⟩
  · intro k α
    exact globalDependentPhysicalMap_regularInverse_leftMul _ hsite F hF
      (regionParentGroundSpace_le_vertexImageGroundSpace _ _ hcover hparent) k
      (fun w => α w.1)
  · intro r α
    exact globalDependentPhysicalMap_regularInverse_rightMul _ F hF torusPlaquetteRegion
      exists_torusPlaquetteRegion_contains_edge P hP Ψ hΨ r α
  · intro α hflat
    obtain ⟨v, hv⟩ := not_forall.mp hflat
    exact globalDependentPhysicalMap_regularInverse_eq_zero_of_torusPlaquetteHolonomy
      _ F hF v (P v) (hP v) Ψ (hΨ v) α hv

end TNLean.PEPS

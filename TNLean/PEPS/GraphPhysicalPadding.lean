/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.GraphDependentCutCoordinates
import TNLean.PEPS.DependentBondLocalInverse
import TNLean.PEPS.GInjectivePhysicalMap

/-!
# Faithful physical padding into the existing graph tensor framework

Independent finite physical alphabets embed into a common finite ambient
alphabet by tagging each coordinate with its vertex. Zero padding preserves
every tensor coefficient, is injective on each site's physical space, and has
an explicit coordinate restriction as a left inverse. The constructed object
is the existing graph PEPS tensor, so its parent is the existing positive
regional parent rather than a replacement definition.
-/

noncomputable section
open scoped BigOperators
namespace TNLean.PEPS
open DependentBondNetwork

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Forget endpoint polarity after locating its unique incident graph edge. -/
def graphEndpointIncident (v : V)
    (p : IncidentEndpoint (graphEdgeTail (Γ := Γ)) graphEdgeHead v) : IncidentEdge Γ v :=
  ⟨p.1.1, by
    rcases p with ⟨⟨e, b⟩, hp⟩
    cases b
    · exact Or.inl hp
    · exact Or.inr hp⟩

omit [Fintype V] [DecidableRel Γ.Adj] in
/-- The ordered graph has no self edges, so endpoint polarity is uniquely recovered. -/
@[simp] theorem graphIncidentEndpoint_endpointIncident (v : V)
    (p : IncidentEndpoint (graphEdgeTail (Γ := Γ)) graphEdgeHead v) :
    graphIncidentEndpoint v (graphEndpointIncident v p) = p := by
  rcases p with ⟨⟨e, b⟩, hp⟩
  cases b
  · have ht : e.1.1 = v := hp
    apply Subtype.ext
    simp [graphIncidentEndpoint, graphEndpointIncident, ht]
  · have hh : e.1.2 = v := hp
    have ht : e.1.1 ≠ v := by rw [← hh]; exact ne_of_lt e.2.1
    apply Subtype.ext
    simp [graphIncidentEndpoint, graphEndpointIncident, ht]

variable (N : Edge Γ → ℕ)
variable {Phys : V → Type*} [∀ v, Fintype (Phys v)]

/-- One finite ambient physical coordinate for each tagged original site coordinate. -/
abbrev physicalPaddingDimension := Fintype.card ((v : V) × Phys v)

/-- The canonical coordinate embedding tags a physical label with its own site. -/
def physicalPaddingEmbedding (v : V) : Phys v ↪ Fin (physicalPaddingDimension (Phys := Phys)) :=
  ⟨fun s ↦ Fintype.equivFin ((v : V) × Phys v) ⟨v, s⟩,
    fun s t h ↦ by
      have hs := (Fintype.equivFin ((v : V) × Phys v)).injective h
      exact eq_of_heq (Sigma.mk.inj_iff.mp hs).2⟩

/-- Zero extension from a site's original physical space to the common ambient space. -/
def physicalPaddingMatrix (v : V) :
    Matrix (Fin (physicalPaddingDimension (Phys := Phys))) (Phys v) ℂ :=
  fun s t ↦ if s = physicalPaddingEmbedding v t then 1 else 0

/-- Coordinate restriction from the ambient space back to each site's own alphabet. -/
def physicalRestrictionMatrix (v : V) :
    Matrix (Phys v) (Fin (physicalPaddingDimension (Phys := Phys))) ℂ :=
  fun t s ↦ if physicalPaddingEmbedding v t = s then 1 else 0

omit [LinearOrder V] in
open scoped Classical in
/-- Restriction is an exact left inverse of zero extension at every site. -/
theorem physicalRestrictionMatrix_mul_padding (v : V) :
    physicalRestrictionMatrix v * physicalPaddingMatrix v = (1 : Matrix (Phys v) (Phys v) ℂ) := by
  classical
  ext s t
  simp [physicalRestrictionMatrix, physicalPaddingMatrix, Matrix.mul_apply, Matrix.one_apply]

omit [LinearOrder V] in
/-- Physical zero padding is injective without any surjectivity requirement. -/
theorem physicalPaddingMatrix_injective (v : V) :
    Function.Injective (Matrix.mulVecLin (physicalPaddingMatrix (Phys := Phys) v)) := by
  classical
  apply Function.LeftInverse.injective (g := Matrix.mulVecLin (physicalRestrictionMatrix v))
  intro x
  change (Matrix.mulVecLin (physicalRestrictionMatrix v) ∘ₗ
    Matrix.mulVecLin (physicalPaddingMatrix v)) x = x
  rw [← Matrix.mulVecLin_mul, physicalRestrictionMatrix_mul_padding, Matrix.mulVecLin_one]
  rfl

/-- The product coordinate restriction is a left inverse of the product zero extension. -/
theorem physicalRestrictionProduct_padding
    (ψ : ((v : V) → Phys v) → ℂ) :
    dependentPhysicalProductFamilyMap physicalRestrictionMatrix
      (dependentPhysicalProductFamilyMap physicalPaddingMatrix ψ) = ψ := by
  change (dependentPhysicalProductFamilyMap physicalRestrictionMatrix ∘ₗ
    dependentPhysicalProductFamilyMap physicalPaddingMatrix) ψ = ψ
  rw [dependentPhysicalProductFamilyMap_comp]
  simp only [physicalRestrictionMatrix_mul_padding, dependentPhysicalProductFamilyMap_one,
    LinearMap.id_apply]

/-- Independent physical zero extensions are injective jointly on the full tensor product. -/
theorem physicalPaddingProduct_injective :
    Function.Injective (dependentPhysicalProductFamilyMap (physicalPaddingMatrix (Phys := Phys))) :=
  Function.LeftInverse.injective physicalRestrictionProduct_padding

/-- The original independently dimensioned sites, zero-padded in the existing
finite-graph tensor type. Virtual bonds keep their original separate dimensions. -/
def graphPhysicalPaddingTensor
    (A : (v : V) → LocalConfig graphEdgeTail graphEdgeHead (fun e ↦ Fin (N e)) v → Phys v → ℂ) :
    Tensor Γ (physicalPaddingDimension (Phys := Phys)) where
  bondDim := N
  component v η s := ∑ t, physicalPaddingMatrix v s t *
    A v (fun p ↦ η (graphEndpointIncident v p)) t

/-- The dependent endpoint reading of the padded graph tensor is exactly
physical zero extension of the original independent tensor family. -/
theorem graphDependentTensor_physicalPadding
    (A : (v : V) → LocalConfig graphEdgeTail graphEdgeHead (fun e ↦ Fin (N e)) v → Phys v → ℂ) :
    graphDependentTensor (graphPhysicalPaddingTensor N A) =
      DependentBondNetwork.physicalMapSite graphEdgeTail graphEdgeHead (fun e ↦ Fin (N e))
        physicalPaddingMatrix A := by
  funext v η s
  change (∑ t, physicalPaddingMatrix v s t *
    A v (fun p ↦ η (graphIncidentEndpoint v (graphEndpointIncident v p))) t) = _
  apply Finset.sum_congr rfl
  intro t _
  congr 2
  funext p
  apply eq_of_heq
  have h := congrArg (fun q ↦ Sigma.mk q (η q))
    (graphIncidentEndpoint_endpointIncident v p)
  exact (Sigma.mk.inj_iff.mp h).2

/-- Restriction after padding recovers every original tensor coefficient. -/
theorem physicalMapSite_restrict_graphPhysicalPaddingTensor
    (A : (v : V) → LocalConfig graphEdgeTail graphEdgeHead (fun e ↦ Fin (N e)) v → Phys v → ℂ) :
    DependentBondNetwork.physicalMapSite graphEdgeTail graphEdgeHead (fun e ↦ Fin (N e))
      physicalRestrictionMatrix (graphDependentTensor (graphPhysicalPaddingTensor N A)) = A := by
  classical
  apply localSiteMap_family_injective graphEdgeTail graphEdgeHead (fun e ↦ Fin (N e))
  intro v
  rw [graphDependentTensor_physicalPadding, localSiteMap_physicalMapSite,
    localSiteMap_physicalMapSite, ← LinearMap.comp_assoc, ← Matrix.mulVecLin_mul,
    physicalRestrictionMatrix_mul_padding, Matrix.mulVecLin_one, LinearMap.id_comp]

/-- Local G-injectivity survives the canonical zero padding, for any chosen
representation of the original virtual space. -/
theorem isGInjective_graphPhysicalPaddingTensor {G : Type*} [Group G]
    (ρ : (v : V) → Representation ℂ G
      (LocalConfig graphEdgeTail graphEdgeHead (fun e ↦ Fin (N e)) v → ℂ))
    (A : (v : V) → LocalConfig graphEdgeTail graphEdgeHead (fun e ↦ Fin (N e)) v → Phys v → ℂ)
    (hA : ∀ v, IsGInjective (ρ v)
      (localSiteMap graphEdgeTail graphEdgeHead (fun e ↦ Fin (N e)) A v)) :
    ∀ v, IsGInjective (ρ v) (localSiteMap graphEdgeTail graphEdgeHead
      (fun e ↦ Fin (N e)) (graphDependentTensor (graphPhysicalPaddingTensor N A)) v) := by
  intro v
  rw [graphDependentTensor_physicalPadding, localSiteMap_physicalMapSite]
  exact (hA v).comp_of_injective _ (physicalPaddingMatrix_injective v)

end TNLean.PEPS

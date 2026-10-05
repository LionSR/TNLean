/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusCutProjectorExpansion
import TNLean.PEPS.TorusCutCoefficientExtraction

/-!
# Applying the local invariant projectors to the actual bond expansion

The product of local invariant projectors fixes every canonical cut vector.
Applied to a bare bond-product vector, it gives the actual canonical PEPS
network with those same bond matrices. These identities allow the derived
flat bond expansion to be reassembled into commuting closure states.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {G V : Type*} [Group G] [Fintype G] [Fintype V] [DecidableEq V]
attribute [local instance] Representation.invertibleFintypeCardComplex

/-- The canonical projector tensor is invariant under its specified local action. -/
theorem representationAveragingSite_invariant
    (ρ : Representation ℂ G ((V × V × V × V) → ℂ)) (g : G) :
    siteMap (representationAveragingSite ρ) ∘ₗ ρ g =
      siteMap (representationAveragingSite ρ) := by
  rw [siteMap_representationAveragingSite]
  change ρ.averageMap * ρ g = ρ.averageMap
  rw [Representation.averageMap, ← Representation.asAlgebraHom_single_one,
    ← map_mul, GroupAlgebra.mul_average_right]

variable {width height : ℕ} [NeZero width] [NeZero height]
local notation "X" => TorusVertex width height

/-- The product of the local virtual invariant projectors, acting on the
exposed physical four-leg coordinates of the canonical tensors. -/
noncomputable def torusSitewiseAveragingProjector
    (ρ : X → Representation ℂ G ((V × V × V × V) → ℂ)) :
    ((X → V × V × V × V) → ℂ) →ₗ[ℂ] ((X → V × V × V × V) → ℂ) :=
  torusSitewisePhysicalMap
    (fun v ↦ LinearMap.toMatrix' (siteMap (representationAveragingSite (ρ v))))

/-- Every canonical cut contraction is fixed by the product local projector. -/
theorem torusSitewiseAveragingProjector_cutMap
    (ρ : X → Representation ℂ G ((V × V × V × V) → ℂ))
    (c : ZMod width) (r : ZMod height)
    (M : TorusCutBoundaryConfig width height V → ℂ) :
    torusSitewiseAveragingProjector ρ
        (torusCutMap (fun v ↦ representationAveragingSite (ρ v)) c r M) =
      torusCutMap (fun v ↦ representationAveragingSite (ρ v)) c r M :=
  torusCutMap_recover_representationAveragingSite ρ _
    (fun v ↦ representationAveragingSite_invariant (ρ v)) c r M

/-- The fixed-point identity extends to every vector in a genuine cut range. -/
theorem torusSitewiseAveragingProjector_eq_self_of_mem_cut
    (ρ : X → Representation ℂ G ((V × V × V × V) → ℂ))
    (c : ZMod width) (r : ZMod height)
    {ψ : (X → V × V × V × V) → ℂ}
    (hψ : ψ ∈ torusCutSpace (fun v ↦ representationAveragingSite (ρ v)) c r) :
    torusSitewiseAveragingProjector ρ ψ = ψ := by
  obtain ⟨M, rfl⟩ := hψ
  exact torusSitewiseAveragingProjector_cutMap ρ c r M

private def identityFourLegSite (t r b l : V) (s : V × V × V × V) : ℂ :=
  if (t, r, b, l) = s then 1 else 0

/-- Projecting an actual bond-product vector gives the canonical network with
exactly its bond matrices. The local action may vary from site to site. -/
theorem torusSitewiseAveragingProjector_bondProduct
    (ρ : X → Representation ℂ G ((V × V × V × V) → ℂ))
    (Uh Uv : X → G →* Matrix V V ℂ) (p : TorusBondLabels width height G) :
    torusSitewiseAveragingProjector ρ (torusRepresentationBondProduct Uh Uv p) =
      fun σ ↦ torusBondNetwork
        (fun v t ↦ representationAveragingSite (ρ v) t.1 t.2.1 t.2.2.1 t.2.2.2 (σ v))
        (fun v ↦ Uh v (p.1 v)) (fun v ↦ Uv v (p.2 v)) := by
  classical
  have hsite (v : X) : physicalMapSite
      (LinearMap.toMatrix' (siteMap (representationAveragingSite (ρ v)))) identityFourLegSite =
        representationAveragingSite (ρ v) := by
    funext t r b l s
    simp [physicalMapSite, identityFourLegSite, siteMap_apply, Pi.single_apply]
  have hnet : torusRepresentationBondProduct Uh Uv p =
      fun σ ↦ torusBondNetwork
        (fun v t ↦ identityFourLegSite t.1 t.2.1 t.2.2.1 t.2.2.2 (σ v))
        (fun v ↦ Uh v (p.1 v)) (fun v ↦ Uv v (p.2 v)) := by
    funext σ
    have hid : (fun (v : X) (t : V × V × V × V) ↦
        identityFourLegSite t.1 t.2.1 t.2.2.1 t.2.2.2 (σ v)) =
        fun v ↦ Pi.single (σ v) 1 := by
      funext v t
      simp only [identityFourLegSite, Pi.single_apply, Prod.eta]
    rw [hid, torusBondNetwork_single]
    rfl
  rw [hnet, torusSitewiseAveragingProjector, torusSitewisePhysicalMap_torusBondNetwork]
  simp_rw [hsite]

end TNLean.PEPS

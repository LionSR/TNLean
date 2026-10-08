/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.NativeTorusParentClassification
import TNLean.PEPS.ParentHamiltonian.TorusNonuniformParentSeamCuts

/-!
# Faithful nonuniform native parent classification

Independent finite physical alphabets are zero-extended to the existing graph
PEPS framework. Its actual positive plaquette parent kernel is exactly the
zero extension of the original native commuting-closure span. Thus every
ambient kernel vector, including any potentially unused coordinates, is
accounted for. Product restriction is the explicit inverse on this kernel.

Source: SCP10, arXiv:1001.3807, Theorems 5.7 and 5.9, expressed in the existing
native simple-graph parent framework by faithful coordinate padding. All edge
dimensions, matching semi-regular representations, site tensors, and physical
alphabets may differ; both native torus periods are at least three.
-/

noncomputable section
namespace TNLean.PEPS
open DependentBondNetwork

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
variable {G : Type*} [Group G] [Finite G]
variable (N : Edge (torusGraph width height) → ℕ)
variable {Phys : TorusVertex width height → Type*} [∀ v, Fintype (Phys v)]
variable (U : (e : Edge (torusGraph width height)) → G →* Matrix (Fin (N e)) (Fin (N e)) ℂ)
variable (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
variable (A : (v : TorusVertex width height) →
  LocalConfig graphEdgeTail graphEdgeHead (fun e ↦ Fin (N e)) v → Phys v → ℂ)
variable (hA : ∀ v, IsGInjective
  (incidentRepresentation graphEdgeTail graphEdgeHead (fun e ↦ Fin (N e)) U v)
  (localSiteMap graphEdgeTail graphEdgeHead (fun e ↦ Fin (N e)) A v))
variable (H : (v : TorusVertex width height) → Matrix
  (RegionPhysicalConfig (d := physicalPaddingDimension (Phys := Phys)) (torusPlaquetteRegion v))
  (RegionPhysicalConfig (d := physicalPaddingDimension (Phys := Phys)) (torusPlaquetteRegion v)) ℂ)
variable (hH : ∀ v, IsRegionParentInteraction (graphPhysicalPaddingTensor N A)
  (torusPlaquetteRegion v) (H v))

include hU hA hH

/-- The full ambient kernel of the existing positive padded parent is exactly
the faithfully embedded original native commuting-closure span. No local-image
or support assumption is imposed on kernel vectors. Source: SCP10, Theorem 5.7. -/
theorem ker_nonuniformTorusPlaquetteParent_eq_map_nativeCommutingClosureSpan :
    (Matrix.mulVecLin (regionParentHamiltonian torusPlaquetteRegion H)).ker =
      (NativeTorus.commutingClosureSpan (fun e ↦ Fin (N e)) U A).map
        (dependentPhysicalProductFamilyMap (physicalPaddingMatrix (Phys := Phys))) := by
  have hB := isGInjective_graphPhysicalPaddingTensor N
    (incidentRepresentation graphEdgeTail graphEdgeHead (fun e ↦ Fin (N e)) U) A hA
  rw [ker_torusPlaquetteParentHamiltonian_eq_nativeCommutingClosureSpan
    (graphPhysicalPaddingTensor N A) U hU hB H hH]
  rw [NativeTorus.map_commutingClosureSpan]
  congr 1
  exact graphDependentTensor_physicalPadding N A

/-- Original physical closure coordinates and the entire ambient parent kernel
are linearly equivalent by zero extension. This identifies no additional vectors. -/
def nonuniformNativeParentEquiv :
    NativeTorus.commutingClosureSpan (fun e ↦ Fin (N e)) U A ≃ₗ[ℂ]
      (Matrix.mulVecLin (regionParentHamiltonian torusPlaquetteRegion H)).ker :=
  (Submodule.equivMapOfInjective
    (dependentPhysicalProductFamilyMap (physicalPaddingMatrix (Phys := Phys)))
    physicalPaddingProduct_injective _).trans
      (LinearEquiv.ofEq _ _
        (ker_nonuniformTorusPlaquetteParent_eq_map_nativeCommutingClosureSpan
          N U hU A hA H hH).symm)

/-- The forward classification equivalence is literally product zero extension. -/
@[simp] theorem nonuniformNativeParentEquiv_apply
    (ψ : NativeTorus.commutingClosureSpan (fun e ↦ Fin (N e)) U A) :
    (nonuniformNativeParentEquiv N U hU A hA H hH ψ :
      (X → Fin (physicalPaddingDimension (Phys := Phys))) → ℂ) =
      dependentPhysicalProductFamilyMap (physicalPaddingMatrix (Phys := Phys)) ψ := rfl

/-- Product restriction is the explicit inverse on every ambient kernel vector. -/
@[simp] theorem nonuniformNativeParentEquiv_symm_apply
    (Ψ : (Matrix.mulVecLin (regionParentHamiltonian torusPlaquetteRegion H)).ker) :
    ((nonuniformNativeParentEquiv N U hU A hA H hH).symm Ψ : ((v : X) → Phys v) → ℂ) =
      dependentPhysicalProductFamilyMap (physicalRestrictionMatrix (Phys := Phys)) Ψ := by
  have heq := congrArg
    (fun z : (Matrix.mulVecLin (regionParentHamiltonian torusPlaquetteRegion H)).ker =>
      dependentPhysicalProductFamilyMap (physicalRestrictionMatrix (Phys := Phys)) z)
    ((nonuniformNativeParentEquiv N U hU A hA H hH).apply_symm_apply Ψ)
  simpa only [nonuniformNativeParentEquiv_apply, physicalRestrictionProduct_padding] using heq

/-- All ambient parent vectors have unique original physical representatives,
and those representatives belong to the actual native commuting-closure span. -/
theorem existsUnique_nativeClosureRepresentative_of_mem_nonuniformParentKernel
    {Ψ : (X → Fin (physicalPaddingDimension (Phys := Phys))) → ℂ}
    (hΨ : Ψ ∈ (Matrix.mulVecLin (regionParentHamiltonian torusPlaquetteRegion H)).ker) :
    ∃! ψ : ((v : X) → Phys v) → ℂ,
      ψ ∈ NativeTorus.commutingClosureSpan (fun e ↦ Fin (N e)) U A ∧
      dependentPhysicalProductFamilyMap (physicalPaddingMatrix (Phys := Phys)) ψ = Ψ := by
  rw [ker_nonuniformTorusPlaquetteParent_eq_map_nativeCommutingClosureSpan N U hU A hA H hH] at hΨ
  obtain ⟨ψ, hψ, heq⟩ := hΨ
  refine ⟨ψ, ⟨hψ, heq⟩, fun χ hχ ↦ ?_⟩
  exact physicalPaddingProduct_injective (hχ.2.trans heq.symm)

/-- The genuine padded parent has exactly one dimension per simultaneous
conjugacy class of commuting pairs, for independent finite physical alphabets.
Source: SCP10, Theorem 5.9, with explicit original-space equivalence. -/
theorem finrank_ker_nonuniformTorusPlaquetteParentHamiltonian :
    Module.finrank ℂ (Matrix.mulVecLin (regionParentHamiltonian torusPlaquetteRegion H)).ker =
      Nat.card (CommutingPairConjugacyClass G) := by
  rw [← (nonuniformNativeParentEquiv N U hU A hA H hH).finrank_eq]
  exact NativeTorus.finrank_commutingClosureSpan (fun e ↦ Fin (N e)) U hU A hA

end TNLean.PEPS

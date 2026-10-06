/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.PaddedPhysicalParent
import TNLean.PEPS.ParentHamiltonian.TorusDependentParentSeamCuts

/-!
# Microscopic parent-to-seam witnesses with independent physical dimensions

Tagging each site's finite physical alphabet realizes its tensor in the existing
finite-simple-graph PEPS parent framework. Every vector in the entire ambient
positive plaquette-parent kernel is the zero extension of a unique original
physical vector. That vector has an actual correlated virtual boundary at every
native seam pair. Thus the coordinate embedding introduces no spurious ground
vectors and no local-image assumption.

Virtual dimensions, matching semi-regular edge representations, physical
dimensions, and G-injective site tensors may all differ. Both native torus periods
are at least three. The result retains all microscopic sites; identifying four
macroscopic blocks with the separate four-block model is not asserted here.

Source: SCP10, arXiv:1001.3807, Theorems 5.4 and 5.5, in the finite native graph
setting, with explicit faithful physical-coordinate padding.
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

/-- Every full ambient parent-kernel vector is the faithful zero extension of
one original, independently dimensioned physical vector with actual boundaries
at every native seam pair. The starting Hamiltonian is the existing graph parent. -/
theorem exists_nonuniform_seamBoundaries_of_mem_torusPlaquetteParentKernel
    (U : (e : Edge Γₜ) → G →* Matrix (Fin (N e)) (Fin (N e)) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
    (A : (v : X) → LocalConfig graphEdgeTail graphEdgeHead (fun e ↦ Fin (N e)) v → Phys v → ℂ)
    (hA : ∀ v, IsGInjective
      (incidentRepresentation graphEdgeTail graphEdgeHead (fun e ↦ Fin (N e)) U v)
      (localSiteMap graphEdgeTail graphEdgeHead (fun e ↦ Fin (N e)) A v))
    (H : (v : X) → Matrix
      (RegionPhysicalConfig (d := physicalPaddingDimension (Phys := Phys)) (torusPlaquetteRegion v))
      (RegionPhysicalConfig (d := physicalPaddingDimension (Phys := Phys))
        (torusPlaquetteRegion v)) ℂ)
    (hH : ∀ v, IsRegionParentInteraction (graphPhysicalPaddingTensor N A)
      (torusPlaquetteRegion v) (H v))
    {Ψ : (X → Fin (physicalPaddingDimension (Phys := Phys))) → ℂ}
    (hΨ : Ψ ∈ (Matrix.mulVecLin (regionParentHamiltonian torusPlaquetteRegion H)).ker) :
    ∃ ψ : ((v : X) → Phys v) → ℂ,
      dependentPhysicalProductFamilyMap (physicalPaddingMatrix (Phys := Phys)) ψ = Ψ ∧
      ∀ (c : ZMod width) (r : ZMod height),
        ∃ M : CutConfig (torusGraphSeamCut c r) (fun e ↦ Fin (N e)) → ℂ,
          ∀ σ, cutCoeff graphEdgeTail graphEdgeHead (fun e ↦ Fin (N e)) A
            (torusGraphSeamCut c r) M σ = ψ σ := by
  let B := graphPhysicalPaddingTensor N A
  have hB := isGInjective_graphPhysicalPaddingTensor N
    (incidentRepresentation graphEdgeTail graphEdgeHead (fun e ↦ Fin (N e)) U) A hA
  have hN := bondDim_ne_zero_of_isSemiRegular B U hU
  rw [ker_regionParentHamiltonian B torusPlaquetteRegion H hH] at hΨ
  refine ⟨dependentPhysicalProductFamilyMap (physicalRestrictionMatrix (Phys := Phys)) Ψ, ?_, ?_⟩
  · exact padding_restriction_eq_self_of_mem_regionParentGroundSpace N A hN (0 : X)
      torusPlaquetteRegion (fun v ↦ ⟨v, mem_torusPlaquetteRegion_self v⟩) hΨ
  · intro c r
    obtain ⟨M, hM⟩ := torusPlaquetteParentGroundSpace_le_graphSeamCut B U hU hB c r hΨ
    refine ⟨M, fun σ ↦ ?_⟩
    have heq := congrArg
      (dependentPhysicalProductFamilyMap (physicalRestrictionMatrix (Phys := Phys))) hM
    exact congrFun ((restriction_cutMap_graphPhysicalPaddingTensor N A
      (torusGraphSeamCut c r) M).symm.trans heq) σ

omit [Fact (2 < width)] [Fact (2 < height)] in
/-- The independently dimensioned physical representative of an ambient
parent vector is unique, including outside any chosen local tensor images. -/
theorem nonuniform_physicalRepresentative_unique
    {ψ χ : ((v : X) → Phys v) → ℂ}
    (h : dependentPhysicalProductFamilyMap (physicalPaddingMatrix (Phys := Phys)) ψ =
      dependentPhysicalProductFamilyMap (physicalPaddingMatrix (Phys := Phys)) χ) : ψ = χ :=
  physicalPaddingProduct_injective h

end TNLean.PEPS

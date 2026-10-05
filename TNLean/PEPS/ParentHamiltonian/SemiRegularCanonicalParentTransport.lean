/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.CopyCanonicalParentTransport
import TNLean.PEPS.ParentHamiltonian.SemiRegularCanonicalLocalTransport

/-!
# Exact canonical parent-kernel transport under multiplicity restoration

The actual global bond map and its adjoint preserve all canonical regional
conditions. Edge-covering parent regions supply the source and target product
supports, so the two maps are inverse on the entire parent ground spaces.
Their restrictions therefore identify the full kernels and their dimensions.

The source has one copy of each supplied matrix block and fourth-root dimension
weights. The target repeats that block by its dimension. When the blocks are
the group-derived distinct irreducibles, the target is the regular representation
in Fourier coordinates. Arbitrary irreducible multiplicities are not treated
by this statement.

Source: SCP10, arXiv:1001.3807, Theorem 5.7 and Section 7, lines 2977–3019.
-/

noncomputable section
open scoped Matrix BigOperators
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {p q : ℕ}

variable {G I : Type*} [Group G] [Fintype G] [Fintype I] [DecidableEq I]

/-- Every actual canonical parent condition is preserved by the global
supported multiplicity-restoring matrix. No coverage is needed for inclusion. -/
theorem graphNumberedMultiplicityMatrix_maps_parent
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (d i)) ≃ Fin q)
    {ι : Type*} (R : ι → Finset V) :
    (regionParentGroundSpace (numberedGraphDressedAveragingTensor
      (blockMatrixRepresentation d D) (blockFourthRootWeight d) eX) R).map
      (Matrix.mulVecLin (graphNumberedBondMatrix eX eY
        (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (d i))))) ≤
      regionParentGroundSpace (numberedGraphDressedAveragingTensor
        (multiplicityRestoredRepresentation d D) 1 eY) R := by
  simpa only [blockMultiplicityRootWeight_self, blockMultiplicityRepresentation_self] using
    graphNumberedCopyMatrix_maps_parent d d D hd eX eY R

/-- The global adjoint preserves the opposite actual canonical parent conditions. -/
theorem graphNumberedMultiplicityMatrix_adjoint_maps_parent
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (d i)) ≃ Fin q)
    {ι : Type*} (R : ι → Finset V) :
    (regionParentGroundSpace (numberedGraphDressedAveragingTensor
      (multiplicityRestoredRepresentation d D) 1 eY) R).map
      (Matrix.mulVecLin (graphNumberedBondMatrix eX eY
        (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (d i)))).conjTranspose) ≤
      regionParentGroundSpace (numberedGraphDressedAveragingTensor
        (blockMatrixRepresentation d D) (blockFourthRootWeight d) eX) R := by
  simpa only [blockMultiplicityRootWeight_self, blockMultiplicityRepresentation_self] using
    graphNumberedCopyMatrix_adjoint_maps_parent d d D hd eX eY R

/-- Canonical source parent constraints supply the full support required to
recover every source ground vector by the global adjoint. -/
theorem graphNumberedMultiplicityMatrix_leftInverse_parent
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (d i)) ≃ Fin q)
    {ι : Type*} (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i)
    {ψ : (V → Fin p) → ℂ}
    (hψ : ψ ∈ regionParentGroundSpace (numberedGraphDressedAveragingTensor
      (blockMatrixRepresentation d D) (blockFourthRootWeight d) eX) R) :
    let M := graphNumberedBondMatrix eX eY
      (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (d i)))
    M.conjTranspose *ᵥ (M *ᵥ ψ) = ψ := by
  simpa only [blockMultiplicityRootWeight_self, blockMultiplicityRepresentation_self] using
    graphNumberedCopyMatrix_leftInverse_parent d d D hd eX eY R hcover hψ

/-- Target canonical parent constraints supply the entire output support,
so the global map recovers every target ground vector from its adjoint image. -/
theorem graphNumberedMultiplicityMatrix_rightInverse_parent
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (d i)) ≃ Fin q)
    {ι : Type*} (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i)
    {ψ : (V → Fin q) → ℂ}
    (hψ : ψ ∈ regionParentGroundSpace (numberedGraphDressedAveragingTensor
      (multiplicityRestoredRepresentation d D) 1 eY) R) :
    let M := graphNumberedBondMatrix eX eY
      (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (d i)))
    M *ᵥ (M.conjTranspose *ᵥ ψ) = ψ := by
  simpa only [blockMultiplicityRootWeight_self, blockMultiplicityRepresentation_self] using
    graphNumberedCopyMatrix_rightInverse_parent d d D hd eX eY R hcover hψ

/-- Multiplicity restoration identifies the entire actual canonical parent
spaces whenever the chosen regions contain every edge. -/
theorem map_regionParentGroundSpace_multiplicity_eq
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (d i)) ≃ Fin q)
    {ι : Type*} (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i) :
    (regionParentGroundSpace (numberedGraphDressedAveragingTensor
      (blockMatrixRepresentation d D) (blockFourthRootWeight d) eX) R).map
      (Matrix.mulVecLin (graphNumberedBondMatrix eX eY
        (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (d i))))) =
      regionParentGroundSpace (numberedGraphDressedAveragingTensor
        (multiplicityRestoredRepresentation d D) 1 eY) R := by
  simpa only [blockMultiplicityRootWeight_self, blockMultiplicityRepresentation_self] using
    map_regionParentGroundSpace_copy_eq d d D hd eX eY R hcover

/-- The physical bond map loses no source canonical parent ground vector. -/
theorem graphNumberedMultiplicityMatrix_injOn_parent
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (d i)) ≃ Fin q)
    {ι : Type*} (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i) :
    Set.InjOn (Matrix.mulVecLin (graphNumberedBondMatrix eX eY
      (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (d i)))))
      (regionParentGroundSpace (numberedGraphDressedAveragingTensor
        (blockMatrixRepresentation d D) (blockFourthRootWeight d) eX) R) := by
  simpa only [blockMultiplicityRootWeight_self, blockMultiplicityRepresentation_self] using
    graphNumberedCopyMatrix_injOn_parent d d D hd eX eY R hcover

/-- Restriction of the actual supported bond map gives a linear equivalence
of the entire canonical parent ground spaces. -/
def canonicalMultiplicityParentEquiv
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (d i)) ≃ Fin q)
    {ι : Type*} (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i) :
    regionParentGroundSpace (numberedGraphDressedAveragingTensor
      (blockMatrixRepresentation d D) (blockFourthRootWeight d) eX) R ≃ₗ[ℂ]
      regionParentGroundSpace (numberedGraphDressedAveragingTensor
        (multiplicityRestoredRepresentation d D) 1 eY) R :=
  canonicalCopyParentEquiv d d D hd eX eY R hcover

/-- The full canonical ground-space dimension is unchanged by multiplicity restoration. -/
theorem finrank_regionParentGroundSpace_multiplicity_eq
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (d i)) ≃ Fin q)
    {ι : Type*} (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i) :
    Module.finrank ℂ (regionParentGroundSpace (numberedGraphDressedAveragingTensor
      (multiplicityRestoredRepresentation d D) 1 eY) R) =
      Module.finrank ℂ (regionParentGroundSpace (numberedGraphDressedAveragingTensor
        (blockMatrixRepresentation d D) (blockFourthRootWeight d) eX) R) := by
  exact (canonicalMultiplicityParentEquiv d D hd eX eY R hcover).symm.finrank_eq

/-- Arbitrary positive canonical parent interactions, with the actual regional
kernels on both sides, have their full Hamiltonian kernels identified by the
physical bond map. The conclusion concerns every ground vector. -/
theorem map_ker_regionParentHamiltonian_multiplicity_eq
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (d i)) ≃ Fin q)
    {ι : Type*} [Fintype ι] (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i)
    (H : (i : ι) → Matrix (RegionPhysicalConfig (d := p) (R i))
      (RegionPhysicalConfig (d := p) (R i)) ℂ)
    (K : (i : ι) → Matrix (RegionPhysicalConfig (d := q) (R i))
      (RegionPhysicalConfig (d := q) (R i)) ℂ)
    (hH : ∀ i, IsRegionParentInteraction (numberedGraphDressedAveragingTensor
      (blockMatrixRepresentation d D) (blockFourthRootWeight d) eX) (R i) (H i))
    (hK : ∀ i, IsRegionParentInteraction (numberedGraphDressedAveragingTensor
      (multiplicityRestoredRepresentation d D) 1 eY) (R i) (K i)) :
    (Matrix.mulVecLin (regionParentHamiltonian R H)).ker.map
      (Matrix.mulVecLin (graphNumberedBondMatrix eX eY
        (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (d i))))) =
      (Matrix.mulVecLin (regionParentHamiltonian R K)).ker := by
  simpa only [blockMultiplicityRootWeight_self, blockMultiplicityRepresentation_self] using
    map_ker_regionParentHamiltonian_copy_eq d d D hd eX eY R hcover H K hH hK

end TNLean.PEPS

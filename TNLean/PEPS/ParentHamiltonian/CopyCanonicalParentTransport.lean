/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.CopyCanonicalLocalTransport
import TNLean.PEPS.ParentHamiltonian.GraphBondPhysicalCoordinates
import TNLean.PEPS.GraphOpenBondRangeSupport
import TNLean.PEPS.SemiRegularBondRetraction

/-!
# Entire canonical parent kernels for arbitrary copy multiplicities

For independent dimensions dᵢ and positive copy counts mᵢ, the source weights
mᵢ^(1/4) and the actual normalized mᵢ-copy bond map identify the canonical
parent kernels with those of the repeated representation. Both local range
inclusions and both global product supports are derived from the actual open
contractions. No ground-space spanning premise is used.

Source: SCP10, arXiv:1001.3807, Theorem 5.7 and Section 7,
lines 2977–3019, with arbitrary positive block multiplicities.
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
theorem graphNumberedCopyMatrix_maps_parent
    (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (m i)) ≃ Fin q)
    {ι : Type*} (R : ι → Finset V) :
    (regionParentGroundSpace (numberedGraphDressedAveragingTensor
      (blockMatrixRepresentation d D) (blockMultiplicityRootWeight d m) eX) R).map
      (Matrix.mulVecLin (graphNumberedBondMatrix eX eY
        (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (m i))))) ≤
      regionParentGroundSpace (numberedGraphDressedAveragingTensor
        (blockMultiplicityRepresentation d m D) 1 eY) R := by
  apply map_regionParentGroundSpace_le_of_blocks
  intro i τ σ
  have hb : regionOperatorBlock (R i)
      (graphNumberedBondMatrix eX eY
        (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (m i)))) τ σ =
      graphMultiplicityBlockCoefficient (fun i => Fin (d i)) (fun i => Fin (m i))
        eX eY (R i) τ σ • numberedRegionCopyMatrix d m eX eY (R i)
          (regionOutsideBoundaryEndpoint eY (R i) τ) := by
    ext y x
    exact regionOperatorBlock_fullMultiplicityBondMap
      (fun i => Fin (d i)) (fun i => Fin (m i)) eX eY (R i) τ σ y x
  rintro _ ⟨φ, hφ, rfl⟩
  change _ *ᵥ φ ∈ _
  rw [hb, Matrix.smul_mulVec]
  exact Submodule.smul_mem _ _
    (numberedRegionCopyMatrix_maps_regionGroundSpace d m D hm eX eY (R i) _
      ⟨φ, hφ, rfl⟩)

/-- The global adjoint preserves the opposite actual canonical parent conditions. -/
theorem graphNumberedCopyMatrix_adjoint_maps_parent
    (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (m i)) ≃ Fin q)
    {ι : Type*} (R : ι → Finset V) :
    (regionParentGroundSpace (numberedGraphDressedAveragingTensor
      (blockMultiplicityRepresentation d m D) 1 eY) R).map
      (Matrix.mulVecLin (graphNumberedBondMatrix eX eY
        (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (m i)))).conjTranspose) ≤
      regionParentGroundSpace (numberedGraphDressedAveragingTensor
        (blockMatrixRepresentation d D) (blockMultiplicityRootWeight d m) eX) R := by
  apply map_regionParentGroundSpace_le_of_blocks
  intro i σ τ
  have hb : regionOperatorBlock (R i)
      (graphNumberedBondMatrix eX eY
        (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (m i)))) τ σ =
      graphMultiplicityBlockCoefficient (fun i => Fin (d i)) (fun i => Fin (m i))
        eX eY (R i) τ σ • numberedRegionCopyMatrix d m eX eY (R i)
          (regionOutsideBoundaryEndpoint eY (R i) τ) := by
    ext y x
    exact regionOperatorBlock_fullMultiplicityBondMap
      (fun i => Fin (d i)) (fun i => Fin (m i)) eX eY (R i) τ σ y x
  rintro _ ⟨φ, hφ, rfl⟩
  change _ *ᵥ φ ∈ _
  rw [regionOperatorBlock_conjTranspose, hb, Matrix.conjTranspose_smul, Matrix.smul_mulVec]
  exact Submodule.smul_mem _ _
    (numberedRegionCopyMatrix_adjoint_maps_regionGroundSpace d m D hm eX eY (R i) _
      ⟨φ, hφ, rfl⟩)

/-- Canonical source parent constraints supply the full support required to
recover every source ground vector by the global adjoint. -/
theorem graphNumberedCopyMatrix_leftInverse_parent
    (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (m i)) ≃ Fin q)
    {ι : Type*} (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i)
    {ψ : (V → Fin p) → ℂ}
    (hψ : ψ ∈ regionParentGroundSpace (numberedGraphDressedAveragingTensor
      (blockMatrixRepresentation d D) (blockMultiplicityRootWeight d m) eX) R) :
    let M := graphNumberedBondMatrix eX eY
      (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (m i)))
    M.conjTranspose *ᵥ (M *ᵥ ψ) = ψ := by
  let : ∀ i, Nonempty (Fin (m i)) := fun i => ⟨⟨0, hm i⟩⟩
  apply (graphBondPhysicalEquiv eX).injective
  rw [graphNumberedBondMatrix_conjTranspose, graphBondPhysicalEquiv_mulVec,
    graphBondPhysicalEquiv_mulVec]
  apply physicalProductMap_fullMultiplicityBondMap_leftInverse
  apply regionParentGroundSpace_mem_product_range_of_factors
    (blockMatrixRepresentation d D) (blockMultiplicityRootWeight d m)
    (blockMultiplicityRootWeight_commute d m D)
    (blockBondInclusion (fun i => Fin (d i))) _ eX R hcover hψ
  intro g
  rw [blockMultiplicityRootWeight_sq_mul]
  exact ⟨_, blockBondInclusion_mulVec (fun i => Fin (d i))
    (fun i => (Real.sqrt (m i : ℝ) : ℂ) • D i g)⟩

/-- Target canonical parent constraints supply the entire output support,
so the global map recovers every target ground vector from its adjoint image. -/
theorem graphNumberedCopyMatrix_rightInverse_parent
    (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (m i)) ≃ Fin q)
    {ι : Type*} (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i)
    {ψ : (V → Fin q) → ℂ}
    (hψ : ψ ∈ regionParentGroundSpace (numberedGraphDressedAveragingTensor
      (blockMultiplicityRepresentation d m D) 1 eY) R) :
    let M := graphNumberedBondMatrix eX eY
      (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (m i)))
    M *ᵥ (M.conjTranspose *ᵥ ψ) = ψ := by
  let : ∀ i, Nonempty (Fin (m i)) := fun i => ⟨⟨0, hm i⟩⟩
  apply (graphBondPhysicalEquiv eY).injective
  rw [graphBondPhysicalEquiv_mulVec, graphNumberedBondMatrix_conjTranspose,
    graphBondPhysicalEquiv_mulVec]
  apply physicalProductMap_fullMultiplicityBondMap_rightInverse
  apply regionParentGroundSpace_mem_product_range_of_factors
    (blockMultiplicityRepresentation d m D) 1 (fun _ => Commute.one_left _)
    (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (m i))) _ eY R hcover hψ
  intro g
  refine ⟨fun r => Matrix.blockDiagonal'
    (fun i => (Real.sqrt (m i : ℝ) : ℂ) • D i g) r.1 r.2, ?_⟩
  simpa [blockMultiplicityRepresentation] using
    fullMultiplicityBondMap_mulVec_sqrt_blockDiagonal
      (fun i => Fin (d i)) (fun i => Fin (m i)) (fun i => D i g)

/-- Multiplicity restoration identifies the entire actual canonical parent
spaces whenever the chosen regions contain every edge. -/
theorem map_regionParentGroundSpace_copy_eq
    (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (m i)) ≃ Fin q)
    {ι : Type*} (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i) :
    (regionParentGroundSpace (numberedGraphDressedAveragingTensor
      (blockMatrixRepresentation d D) (blockMultiplicityRootWeight d m) eX) R).map
      (Matrix.mulVecLin (graphNumberedBondMatrix eX eY
        (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (m i))))) =
      regionParentGroundSpace (numberedGraphDressedAveragingTensor
        (blockMultiplicityRepresentation d m D) 1 eY) R := by
  apply le_antisymm (graphNumberedCopyMatrix_maps_parent d m D hm eX eY R)
  intro ψ hψ
  refine ⟨(graphNumberedBondMatrix eX eY
    (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (m i)))).conjTranspose *ᵥ ψ,
    ?_, graphNumberedCopyMatrix_rightInverse_parent d m D hm eX eY R hcover hψ⟩
  exact graphNumberedCopyMatrix_adjoint_maps_parent d m D hm eX eY R ⟨ψ, hψ, rfl⟩

/-- The physical bond map loses no source canonical parent ground vector. -/
theorem graphNumberedCopyMatrix_injOn_parent
    (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (m i)) ≃ Fin q)
    {ι : Type*} (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i) :
    Set.InjOn (Matrix.mulVecLin (graphNumberedBondMatrix eX eY
      (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (m i)))))
      (regionParentGroundSpace (numberedGraphDressedAveragingTensor
        (blockMatrixRepresentation d D) (blockMultiplicityRootWeight d m) eX) R) := by
  intro ψ hψ φ hφ hEq
  have h := congrArg (fun x => (graphNumberedBondMatrix eX eY
    (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (m i)))).conjTranspose *ᵥ x) hEq
  change _ *ᵥ (_ *ᵥ ψ) = _ *ᵥ (_ *ᵥ φ) at h
  rwa [graphNumberedCopyMatrix_leftInverse_parent d m D hm eX eY R hcover hψ,
    graphNumberedCopyMatrix_leftInverse_parent d m D hm eX eY R hcover hφ] at h

/-- Restriction of the actual supported bond map gives a linear equivalence
of the entire canonical parent ground spaces. -/
def canonicalCopyParentEquiv
    (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (m i)) ≃ Fin q)
    {ι : Type*} (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i) :
    regionParentGroundSpace (numberedGraphDressedAveragingTensor
      (blockMatrixRepresentation d D) (blockMultiplicityRootWeight d m) eX) R ≃ₗ[ℂ]
      regionParentGroundSpace (numberedGraphDressedAveragingTensor
        (blockMultiplicityRepresentation d m D) 1 eY) R :=
  LinearEquiv.ofBijective
    (((Matrix.mulVecLin (graphNumberedBondMatrix eX eY
      (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (m i))))) ∘ₗ
      (regionParentGroundSpace (numberedGraphDressedAveragingTensor
        (blockMatrixRepresentation d D)
          (blockMultiplicityRootWeight d m) eX) R).subtype).codRestrict _
      (fun ψ => graphNumberedCopyMatrix_maps_parent d m D hm eX eY R ⟨ψ, ψ.2, rfl⟩))
    ⟨fun ψ φ h => Subtype.ext (graphNumberedCopyMatrix_injOn_parent
        d m D hm eX eY R hcover ψ.2 φ.2 (congrArg Subtype.val h)), by
      intro ψ
      have hψ := (map_regionParentGroundSpace_copy_eq d m D hm eX eY R hcover).ge ψ.2
      obtain ⟨φ, hφ, hEq⟩ := hψ
      exact ⟨⟨φ, hφ⟩, Subtype.ext hEq⟩⟩

/-- The full canonical ground-space dimension is unchanged by multiplicity restoration. -/
theorem finrank_regionParentGroundSpace_copy_eq
    (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (m i)) ≃ Fin q)
    {ι : Type*} (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i) :
    Module.finrank ℂ (regionParentGroundSpace (numberedGraphDressedAveragingTensor
      (blockMultiplicityRepresentation d m D) 1 eY) R) =
      Module.finrank ℂ (regionParentGroundSpace (numberedGraphDressedAveragingTensor
        (blockMatrixRepresentation d D) (blockMultiplicityRootWeight d m) eX) R) :=
  (canonicalCopyParentEquiv d m D hm eX eY R hcover).symm.finrank_eq

/-- Arbitrary positive canonical parent interactions, with the actual regional
kernels on both sides, have their full Hamiltonian kernels identified by the
physical bond map. The conclusion concerns every ground vector. -/
theorem map_ker_regionParentHamiltonian_copy_eq
    (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (m i)) ≃ Fin q)
    {ι : Type*} [Fintype ι] (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i)
    (H : (i : ι) → Matrix (RegionPhysicalConfig (d := p) (R i))
      (RegionPhysicalConfig (d := p) (R i)) ℂ)
    (K : (i : ι) → Matrix (RegionPhysicalConfig (d := q) (R i))
      (RegionPhysicalConfig (d := q) (R i)) ℂ)
    (hH : ∀ i, IsRegionParentInteraction (numberedGraphDressedAveragingTensor
      (blockMatrixRepresentation d D) (blockMultiplicityRootWeight d m) eX) (R i) (H i))
    (hK : ∀ i, IsRegionParentInteraction (numberedGraphDressedAveragingTensor
      (blockMultiplicityRepresentation d m D) 1 eY) (R i) (K i)) :
    (Matrix.mulVecLin (regionParentHamiltonian R H)).ker.map
      (Matrix.mulVecLin (graphNumberedBondMatrix eX eY
        (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (m i))))) =
      (Matrix.mulVecLin (regionParentHamiltonian R K)).ker := by
  rw [ker_regionParentHamiltonian _ R H hH, ker_regionParentHamiltonian _ R K hK]
  exact map_regionParentGroundSpace_copy_eq d m D hm eX eY R hcover

end TNLean.PEPS

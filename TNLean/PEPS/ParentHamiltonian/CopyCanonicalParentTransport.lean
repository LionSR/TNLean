/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.OrientedCopyParentTransport

/-!
# Entire canonical parent kernels for arbitrary copy multiplicities

For independent dimensions dᵢ and positive copy counts mᵢ, the source weights
mᵢ^(1/4) and the actual normalized mᵢ-copy bond map identify the canonical
parent kernels with those of the repeated representation. Both local range
inclusions and both global product supports are derived from the actual open
contractions. No ground-space spanning premise is used. Each statement is the
case of the oriented copy transport in which no edge is reversed.

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
  simpa only [numberedGraphOrientedAveragingTensor_false] using
    graphNumberedCopyMatrix_maps_oriented_parent (fun _ => false) d m D hm eX eY R

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
  simpa only [numberedGraphOrientedAveragingTensor_false] using
    graphNumberedCopyMatrix_adjoint_maps_oriented_parent (fun _ => false) d m D hm eX eY R

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
    M.conjTranspose *ᵥ (M *ᵥ ψ) = ψ :=
  graphNumberedCopyMatrix_leftInverse_oriented_parent (fun _ => false) d m D hm eX eY R hcover
    (by rwa [numberedGraphOrientedAveragingTensor_false])

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
    M *ᵥ (M.conjTranspose *ᵥ ψ) = ψ :=
  graphNumberedCopyMatrix_rightInverse_oriented_parent (fun _ => false) d m D hm eX eY R hcover
    (by rwa [numberedGraphOrientedAveragingTensor_false])

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
  simpa only [numberedGraphOrientedAveragingTensor_false] using
    map_regionParentGroundSpace_oriented_copy_eq (fun _ => false) d m D hm eX eY R hcover

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
  simpa only [numberedGraphOrientedAveragingTensor_false] using
    graphNumberedCopyMatrix_injOn_oriented_parent (fun _ => false) d m D hm eX eY R hcover

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
  LinearMap.submoduleEquivOfInjOn _
    (graphNumberedCopyMatrix_injOn_parent d m D hm eX eY R hcover)
    (map_regionParentGroundSpace_copy_eq d m D hm eX eY R hcover)

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

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.OrientedCoordinateParentTransport

/-!
# Fourier transport of canonical regional parent conditions

Every exterior matrix block of the literal global Fourier bond operation
carries the actual regional contraction range into the target range.
Consequently arbitrary families of canonical regional parent conditions
transform covariantly, without any assumption about their joint kernel.
The global statements are the case of the oriented Fourier transport in which
no edge is reversed.

Source: SCP10, arXiv:1001.3807, Theorem 5.7 and Section 7, lines 2938–3019.
-/

noncomputable section
open scoped Matrix BigOperators
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G X Y : Type*} [Group G] [Fintype G]
variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] {p q : ℕ}

/-- Every exterior block of the global Fourier bond matrix sends the actual
numbered regional PEPS range into the target range. -/
theorem regionOperatorBlock_graphNumberedBondMatrix_coordinates_maps
    (Q : Matrix Y X ℂ) (hQ : Q.conjTranspose * Q = 1)
    (U : G →* Matrix X X ℂ) (L : G →* Matrix Y Y ℂ)
    (hL : ∀ g, L g = Q * U g * Q.conjTranspose)
    (eX : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Y) ≃ Fin q)
    (R : Finset V)
    (τ : RegionPhysicalConfig (d := q) (Finset.univ \ R))
    (σ : RegionPhysicalConfig (d := p) (Finset.univ \ R)) :
    (regionGroundSpace (numberedGraphDressedAveragingTensor U 1 eX) R).map
      (Matrix.mulVecLin (regionOperatorBlock R
        (graphNumberedBondMatrix eX eY (bondCoordinateMatrix Q)) τ σ)) ≤
      regionGroundSpace (numberedGraphDressedAveragingTensor L 1 eY) R := by
  simpa only [numberedGraphOrientedAveragingTensor_false,
    graphNumberedBondFamilyMatrix_orientedBondCoordinateMatrix_false] using
    regionOperatorBlock_graphNumberedBondFamilyMatrix_oriented_coordinates_maps
      Q hQ U L hL (fun _ => false) eX eY R τ σ

/-- The actual global Fourier operation preserves every canonical parent
condition in an arbitrary family of regions. -/
theorem graphNumberedBondMatrix_coordinates_maps_regionParentGroundSpace
    {ι : Type*} (Q : Matrix Y X ℂ) (hQ : Q.conjTranspose * Q = 1)
    (U : G →* Matrix X X ℂ) (L : G →* Matrix Y Y ℂ)
    (hL : ∀ g, L g = Q * U g * Q.conjTranspose)
    (eX : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Y) ≃ Fin q) (R : ι → Finset V) :
    (regionParentGroundSpace (numberedGraphDressedAveragingTensor U 1 eX) R).map
      (Matrix.mulVecLin (graphNumberedBondMatrix eX eY (bondCoordinateMatrix Q))) ≤
      regionParentGroundSpace (numberedGraphDressedAveragingTensor L 1 eY) R := by
  simpa only [numberedGraphOrientedAveragingTensor_false,
    graphNumberedBondFamilyMatrix_orientedBondCoordinateMatrix_false] using
    graphNumberedBondFamilyMatrix_oriented_coordinates_maps_regionParentGroundSpace
      Q hQ U L hL (fun _ => false) eX eY R

omit [DecidableEq X] [Fintype Y] in
/-- The actual global Fourier map cancels against the inverse coordinate map
on every physical vector, not only on closed PEPS vectors. -/
theorem graphNumberedBondMatrix_coordinates_rightInverse [Finite Y]
    (Q : Matrix Y X ℂ) (hQ : Q * Q.conjTranspose = 1)
    (eX : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Y) ≃ Fin q)
    (ψ : (V → Fin q) → ℂ) :
    graphNumberedBondMatrix eX eY (bondCoordinateMatrix Q) *ᵥ
      (graphNumberedBondMatrix eY eX (bondCoordinateMatrix Q.conjTranspose) *ᵥ ψ) = ψ :=
  graphNumberedBondFamilyMatrix_oriented_coordinates_rightInverse Q hQ (fun _ => false) eX eY ψ

/-- Equality of the entire canonical parent ground spaces under the actual
Fourier operation. No coverage condition on the region family is needed. -/
theorem map_regionParentGroundSpace_coordinates_eq
    {ι : Type*} (Q : Matrix Y X ℂ) (hQ : Q.conjTranspose * Q = 1)
    (U : G →* Matrix X X ℂ) (L : G →* Matrix Y Y ℂ)
    (hL : ∀ g, L g = Q * U g * Q.conjTranspose)
    (eX : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Y) ≃ Fin q) (R : ι → Finset V) :
    (regionParentGroundSpace (numberedGraphDressedAveragingTensor U 1 eX) R).map
      (Matrix.mulVecLin (graphNumberedBondMatrix eX eY (bondCoordinateMatrix Q))) =
      regionParentGroundSpace (numberedGraphDressedAveragingTensor L 1 eY) R := by
  simpa only [numberedGraphOrientedAveragingTensor_false,
    graphNumberedBondFamilyMatrix_orientedBondCoordinateMatrix_false] using
    map_regionParentGroundSpace_oriented_coordinates_eq Q hQ U L hL (fun _ => false) eX eY R

omit [DecidableEq Y] [Fintype X] in
/-- The Fourier bond matrix loses no physical vector. -/
theorem graphNumberedBondMatrix_coordinates_injective [Finite X]
    (Q : Matrix Y X ℂ) (hQ : Q.conjTranspose * Q = 1)
    (eX : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Y) ≃ Fin q) :
    Function.Injective (Matrix.mulVecLin
      (graphNumberedBondMatrix eX eY (bondCoordinateMatrix Q))) :=
  graphNumberedBondFamilyMatrix_oriented_coordinates_injective Q hQ (fun _ => false) eX eY

/-- Restriction of the actual Fourier operation is a linear equivalence of
canonical parent ground spaces for every region family. -/
def canonicalCoordinateParentEquiv
    {ι : Type*} (Q : Matrix Y X ℂ) (hQ : Q.conjTranspose * Q = 1)
    (U : G →* Matrix X X ℂ) (L : G →* Matrix Y Y ℂ)
    (hL : ∀ g, L g = Q * U g * Q.conjTranspose)
    (eX : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Y) ≃ Fin q) (R : ι → Finset V) :
    regionParentGroundSpace (numberedGraphDressedAveragingTensor U 1 eX) R ≃ₗ[ℂ]
      regionParentGroundSpace (numberedGraphDressedAveragingTensor L 1 eY) R :=
  LinearMap.submoduleEquivOfInjOn _
    (graphNumberedBondMatrix_coordinates_injective Q hQ eX eY).injOn
    (map_regionParentGroundSpace_coordinates_eq Q hQ U L hL eX eY R)

/-- The dimension of the entire canonical parent kernel is coordinate invariant. -/
theorem finrank_regionParentGroundSpace_coordinates_eq
    {ι : Type*} (Q : Matrix Y X ℂ) (hQ : Q.conjTranspose * Q = 1)
    (U : G →* Matrix X X ℂ) (L : G →* Matrix Y Y ℂ)
    (hL : ∀ g, L g = Q * U g * Q.conjTranspose)
    (eX : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Y) ≃ Fin q) (R : ι → Finset V) :
    Module.finrank ℂ (regionParentGroundSpace (numberedGraphDressedAveragingTensor L 1 eY) R) =
      Module.finrank ℂ (regionParentGroundSpace (numberedGraphDressedAveragingTensor U 1 eX) R) :=
  (canonicalCoordinateParentEquiv Q hQ U L hL eX eY R).symm.finrank_eq

/-- Fourier coordinates identify full kernels of arbitrary positive canonical
parent interactions, retaining their actual regional PEPS ranges. -/
theorem map_ker_regionParentHamiltonian_coordinates_eq
    {ι : Type*} [Fintype ι] (Q : Matrix Y X ℂ) (hQ : Q.conjTranspose * Q = 1)
    (U : G →* Matrix X X ℂ) (L : G →* Matrix Y Y ℂ)
    (hL : ∀ g, L g = Q * U g * Q.conjTranspose)
    (eX : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Y) ≃ Fin q) (R : ι → Finset V)
    (H : (i : ι) → Matrix (RegionPhysicalConfig (d := p) (R i))
      (RegionPhysicalConfig (d := p) (R i)) ℂ)
    (K : (i : ι) → Matrix (RegionPhysicalConfig (d := q) (R i))
      (RegionPhysicalConfig (d := q) (R i)) ℂ)
    (hH : ∀ i, IsRegionParentInteraction (numberedGraphDressedAveragingTensor U 1 eX)
      (R i) (H i))
    (hK : ∀ i, IsRegionParentInteraction (numberedGraphDressedAveragingTensor L 1 eY)
      (R i) (K i)) :
    (Matrix.mulVecLin (regionParentHamiltonian R H)).ker.map
      (Matrix.mulVecLin (graphNumberedBondMatrix eX eY (bondCoordinateMatrix Q))) =
      (Matrix.mulVecLin (regionParentHamiltonian R K)).ker := by
  rw [ker_regionParentHamiltonian _ R H hH, ker_regionParentHamiltonian _ R K hK]
  exact map_regionParentGroundSpace_coordinates_eq Q hQ U L hL eX eY R

end TNLean.PEPS

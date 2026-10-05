/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GraphOpenBondCoordinateTransport
import TNLean.PEPS.ParentHamiltonian.SemiRegularCanonicalParentTransport

/-!
# Fourier transport of canonical regional parent conditions

Every exterior matrix block of the literal global Fourier bond operation
carries the actual regional contraction range into the target range.
Consequently arbitrary families of canonical regional parent conditions
transform covariantly, without any assumption about their joint kernel.

Source: SCP10, arXiv:1001.3807, Theorem 5.7 and Section 7, lines 2938–3019.
-/

noncomputable section
open scoped Matrix BigOperators
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
private abbrev RI (R : Finset V) := {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}
private abbrev RB (R : Finset V) := {e : Edge Γ // IsRegionBoundaryEdge R e}
variable {G X Y : Type*} [Group G] [Fintype G]
variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] {p q : ℕ}

/-- The scalar supplied by the fixed exterior endpoint of every crossing bond. -/
def graphBoundaryExteriorCoordinateCoefficient (Q : Matrix Y X ℂ) (R : Finset V)
    (γY : RB (Γ := Γ) R → Y) (γX : RB (Γ := Γ) R → X) : ℂ :=
  ∏ e, if e.1.1.1 ∈ R then Q (γY e) (γX e) else star (Q (γY e) (γX e))

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
/-- Crossing Fourier blocks factor into a fixed exterior scalar and the
oriented regional Fourier operation. -/
theorem mixedPhysicalProductMatrix_boundary_coordinates
    (Q : Matrix Y X ℂ) (R : Finset V)
    (γY : RB (Γ := Γ) R → Y) (γX : RB (Γ := Γ) R → X) :
    mixedPhysicalProductMatrix (graphBoundaryBondMatrix (bondCoordinateMatrix Q) R γY γX)
      (fun _ : RI (Γ := Γ) R => bondCoordinateMatrix Q) =
      graphBoundaryExteriorCoordinateCoefficient Q R γY γX • graphRegionCoordinateMatrix Q R := by
  ext τ σ
  have hb (e : RB (Γ := Γ) R) :
      graphBoundaryBondMatrix (bondCoordinateMatrix Q) R γY γX e (τ.1 e) (σ.1 e) =
        (if e.1.1.1 ∈ R then Q (γY e) (γX e) else star (Q (γY e) (γX e))) *
          graphBoundaryCoordinateMatrix Q R e (τ.1 e) (σ.1 e) := by
    unfold graphBoundaryBondMatrix graphBoundaryCoordinateMatrix
    split_ifs <;> simp [bondCoordinateMatrix, mul_comm]
  simp only [mixedPhysicalProductMatrix, hb, Finset.prod_mul_distrib,
    graphBoundaryExteriorCoordinateCoefficient, graphRegionCoordinateMatrix,
    Matrix.smul_apply, smul_eq_mul]
  rw [mul_assoc]

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
  let c := graphExteriorBondCoefficient eX eY (bondCoordinateMatrix Q) R τ σ *
    graphBoundaryExteriorCoordinateCoefficient Q R
      (regionOutsideBoundaryEndpoint eY R τ) (regionOutsideBoundaryEndpoint eX R σ)
  have hblock : regionOperatorBlock R
      (graphNumberedBondMatrix eX eY (bondCoordinateMatrix Q)) τ σ =
      c • (graphRegionCoordinateMatrix Q R).submatrix
        (regionBondConfigEquiv eY R) (regionBondConfigEquiv eX R) := by
    ext y x
    rw [regionOperatorBlock_graphNumberedBondMatrix,
      mixedPhysicalProductMatrix_boundary_coordinates]
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.submatrix_apply, c, mul_assoc]
  rintro _ ⟨ψ, hψ, rfl⟩
  rw [hblock, Matrix.mulVecLin_apply, Matrix.smul_mulVec]
  apply Submodule.smul_mem
  apply (regionBondPhysicalEquiv_mem_graphOpenBondSpace_iff _ _
    (fun _ => Commute.one_left _) eY R _).mp
  have hs := (regionBondPhysicalEquiv_mem_graphOpenBondSpace_iff _ _
    (fun _ => Commute.one_left _) eX R ψ).mpr hψ
  have ht := graphRegionCoordinateMatrix_maps_openBondSpace Q hQ U L hL R
    ⟨regionBondPhysicalEquiv eX R ψ, hs, rfl⟩
  convert ht using 1
  funext β
  change ((graphRegionCoordinateMatrix Q R).submatrix
    (regionBondConfigEquiv eY R) (regionBondConfigEquiv eX R) *ᵥ ψ)
      ((regionBondConfigEquiv eY R).symm β) = _
  rw [Matrix.submatrix_mulVec_equiv]
  simp only [Function.comp_apply, Equiv.apply_symm_apply]
  rfl

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
      regionParentGroundSpace (numberedGraphDressedAveragingTensor L 1 eY) R :=
  map_regionParentGroundSpace_le_of_blocks _ _ R _ fun i τ σ =>
    regionOperatorBlock_graphNumberedBondMatrix_coordinates_maps Q hQ U L hL eX eY (R i) τ σ

omit [DecidableEq X] [Fintype Y] in
/-- The actual global Fourier map cancels against the inverse coordinate map
on every physical vector, not only on closed PEPS vectors. -/
theorem graphNumberedBondMatrix_coordinates_rightInverse [Finite Y]
    (Q : Matrix Y X ℂ) (hQ : Q * Q.conjTranspose = 1)
    (eX : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Y) ≃ Fin q)
    (ψ : (V → Fin q) → ℂ) :
    graphNumberedBondMatrix eX eY (bondCoordinateMatrix Q) *ᵥ
      (graphNumberedBondMatrix eY eX (bondCoordinateMatrix Q.conjTranspose) *ᵥ ψ) = ψ := by
  let := Fintype.ofFinite Y
  apply (graphBondPhysicalEquiv eY).injective
  rw [graphBondPhysicalEquiv_mulVec, graphBondPhysicalEquiv_mulVec]
  simp only [physicalProductMap, Matrix.mulVecLin_apply]
  rw [Matrix.mulVec_mulVec, physicalProductMatrix_mul, bondCoordinateMatrix_mul,
    hQ, bondCoordinateMatrix_one]
  have hi : physicalProductMatrix (Edge Γ) (1 : Matrix (Y × Y) (Y × Y) ℂ) = 1 := by
    ext τ σ
    simp only [physicalProductMatrix, Matrix.one_apply, Fintype.prod_boole, funext_iff]
  rw [hi, Matrix.one_mulVec]

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
  apply le_antisymm
    (graphNumberedBondMatrix_coordinates_maps_regionParentGroundSpace Q hQ U L hL eX eY R)
  intro ψ hψ
  have hQQ := mul_conjTranspose_eq_one_of_representation_coordinates Q U L hL
  have hinv : ∀ g, U g = Q.conjTranspose * L g * Q.conjTranspose.conjTranspose := by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      representation_coordinates_conjTranspose Q hQ U L hL
  refine ⟨graphNumberedBondMatrix eY eX (bondCoordinateMatrix Q.conjTranspose) *ᵥ ψ,
    ?_, graphNumberedBondMatrix_coordinates_rightInverse Q hQQ eX eY ψ⟩
  exact graphNumberedBondMatrix_coordinates_maps_regionParentGroundSpace Q.conjTranspose
    (by simpa only [Matrix.conjTranspose_conjTranspose] using hQQ) L U hinv eY eX R
      ⟨ψ, hψ, rfl⟩

omit [DecidableEq Y] [Fintype X] in
/-- The Fourier bond matrix loses no physical vector. -/
theorem graphNumberedBondMatrix_coordinates_injective [Finite X]
    (Q : Matrix Y X ℂ) (hQ : Q.conjTranspose * Q = 1)
    (eX : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Y) ≃ Fin q) :
    Function.Injective (Matrix.mulVecLin
      (graphNumberedBondMatrix eX eY (bondCoordinateMatrix Q))) := by
  let := Fintype.ofFinite X
  intro ψ φ h
  have hc (χ : (V → Fin p) → ℂ) :
      graphNumberedBondMatrix eY eX (bondCoordinateMatrix Q.conjTranspose) *ᵥ
        (graphNumberedBondMatrix eX eY (bondCoordinateMatrix Q) *ᵥ χ) = χ := by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      graphNumberedBondMatrix_coordinates_rightInverse Q.conjTranspose
        (by simpa only [Matrix.conjTranspose_conjTranspose] using hQ) eY eX χ
  have he := congrArg (fun χ =>
    graphNumberedBondMatrix eY eX (bondCoordinateMatrix Q.conjTranspose) *ᵥ χ) h
  change _ *ᵥ (_ *ᵥ ψ) = _ *ᵥ (_ *ᵥ φ) at he
  rwa [hc, hc] at he

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
  LinearEquiv.ofBijective
    (((Matrix.mulVecLin (graphNumberedBondMatrix eX eY (bondCoordinateMatrix Q))) ∘ₗ
      (regionParentGroundSpace (numberedGraphDressedAveragingTensor U 1 eX) R).subtype).codRestrict
        _ (fun ψ =>
          graphNumberedBondMatrix_coordinates_maps_regionParentGroundSpace
            Q hQ U L hL eX eY R ⟨ψ, ψ.2, rfl⟩))
    ⟨fun ψ φ h => Subtype.ext (graphNumberedBondMatrix_coordinates_injective Q hQ eX eY
        (congrArg Subtype.val h)), by
      intro ψ
      have hψ := (map_regionParentGroundSpace_coordinates_eq Q hQ U L hL eX eY R).ge ψ.2
      obtain ⟨φ, hφ, hEq⟩ := hψ
      exact ⟨⟨φ, hφ⟩, Subtype.ext hEq⟩⟩

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

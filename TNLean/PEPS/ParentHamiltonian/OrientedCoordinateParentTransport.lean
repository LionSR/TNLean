/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GraphOrientedCoordinateTransport
import TNLean.PEPS.GraphBondFamilyRegionBlocks
import TNLean.PEPS.ParentHamiltonian.GraphCoordinateCanonicalParentTransport

/-!
# Canonical parent transport with arbitrary edge orientations

Each regional block of the actual orientation-dependent Fourier operation
transports the full regional range. The ambient operation is invertible,
so every family of canonical parent spaces is linearly equivalent without
any coverage assumption on that family.

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

/-- The scalar contributed by the fixed exterior endpoint of each crossing
bond, with the arbitrary edge orientation retained. -/
def graphOrientedBoundaryExteriorCoordinateCoefficient (Q : Matrix Y X ℂ)
    (o : Edge Γ → Bool) (R : Finset V)
    (γY : RB (Γ := Γ) R → Y) (γX : RB (Γ := Γ) R → X) : ℂ :=
  ∏ e, if e.1.1.1 ∈ R then graphOrientedEdgeCoordinateMatrix Q o e.1 (γY e) (γX e)
    else star (graphOrientedEdgeCoordinateMatrix Q o e.1 (γY e) (γX e))

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
/-- Every crossing block factors into its exterior scalar and the actual
oriented regional coordinate operation. -/
theorem mixedPhysicalProductMatrix_oriented_boundary_coordinates
    (Q : Matrix Y X ℂ) (o : Edge Γ → Bool) (R : Finset V)
    (γY : RB (Γ := Γ) R → Y) (γX : RB (Γ := Γ) R → X) :
    mixedPhysicalProductMatrix
      (graphBoundaryBondFamilyMatrix (graphOrientedBondCoordinateMatrix Q o) R γY γX)
      (fun e : RI (Γ := Γ) R => graphOrientedBondCoordinateMatrix Q o e.1) =
      graphOrientedBoundaryExteriorCoordinateCoefficient Q o R γY γX •
        graphOrientedRegionCoordinateMatrix Q o R := by
  ext τ σ
  have hb (e : RB (Γ := Γ) R) :
      graphBoundaryBondFamilyMatrix (graphOrientedBondCoordinateMatrix Q o) R γY γX e
        (τ.1 e) (σ.1 e) =
        (if e.1.1.1 ∈ R then graphOrientedEdgeCoordinateMatrix Q o e.1 (γY e) (γX e)
          else star (graphOrientedEdgeCoordinateMatrix Q o e.1 (γY e) (γX e))) *
          graphOrientedBoundaryCoordinateMatrix Q o R e (τ.1 e) (σ.1 e) := by
    unfold graphBoundaryBondFamilyMatrix graphOrientedBoundaryCoordinateMatrix
    split_ifs <;> simp [graphOrientedBondCoordinateMatrix, bondCoordinateMatrix, mul_comm]
  simp only [mixedPhysicalProductMatrix, hb, Finset.prod_mul_distrib,
    graphOrientedBoundaryExteriorCoordinateCoefficient, graphOrientedRegionCoordinateMatrix,
    Matrix.smul_apply, smul_eq_mul]
  rw [mul_assoc]

/-- Every exterior block of the global Fourier bond matrix sends the actual
numbered regional PEPS range into the target range. -/
theorem regionOperatorBlock_graphNumberedBondFamilyMatrix_oriented_coordinates_maps
    (Q : Matrix Y X ℂ) (hQ : Q.conjTranspose * Q = 1)
    (U : G →* Matrix X X ℂ) (L : G →* Matrix Y Y ℂ)
    (hL : ∀ g, L g = Q * U g * Q.conjTranspose) (o : Edge Γ → Bool)
    (eX : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Y) ≃ Fin q)
    (R : Finset V)
    (τ : RegionPhysicalConfig (d := q) (Finset.univ \ R))
    (σ : RegionPhysicalConfig (d := p) (Finset.univ \ R)) :
    (regionGroundSpace (numberedGraphOrientedAveragingTensor U 1 o eX) R).map
      (Matrix.mulVecLin (regionOperatorBlock R
        (graphNumberedBondFamilyMatrix eX eY (graphOrientedBondCoordinateMatrix Q o)) τ σ)) ≤
      regionGroundSpace (numberedGraphOrientedAveragingTensor L 1 o eY) R := by
  let c := graphExteriorBondFamilyCoefficient eX eY (graphOrientedBondCoordinateMatrix Q o) R τ σ *
    graphOrientedBoundaryExteriorCoordinateCoefficient Q o R
      (regionOutsideBoundaryEndpoint eY R τ) (regionOutsideBoundaryEndpoint eX R σ)
  have hblock : regionOperatorBlock R
      (graphNumberedBondFamilyMatrix eX eY (graphOrientedBondCoordinateMatrix Q o)) τ σ =
      c • (graphOrientedRegionCoordinateMatrix Q o R).submatrix
        (regionBondConfigEquiv eY R) (regionBondConfigEquiv eX R) := by
    ext y x
    rw [regionOperatorBlock_graphNumberedBondFamilyMatrix,
      mixedPhysicalProductMatrix_oriented_boundary_coordinates]
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.submatrix_apply, c, mul_assoc]
  rintro _ ⟨ψ, hψ, rfl⟩
  rw [hblock, Matrix.mulVecLin_apply, Matrix.smul_mulVec]
  apply Submodule.smul_mem
  apply (regionBondPhysicalEquiv_mem_graphOrientedOpenBondSpace_iff _ _
    (fun _ => Commute.one_left _) o eY R _).mp
  have hs := (regionBondPhysicalEquiv_mem_graphOrientedOpenBondSpace_iff _ _
    (fun _ => Commute.one_left _) o eX R ψ).mpr hψ
  have ht := graphOrientedRegionCoordinateMatrix_maps_openBondSpace Q hQ U L hL o R
    ⟨regionBondPhysicalEquiv eX R ψ, hs, rfl⟩
  convert ht using 1
  funext β
  change ((graphOrientedRegionCoordinateMatrix Q o R).submatrix
    (regionBondConfigEquiv eY R) (regionBondConfigEquiv eX R) *ᵥ ψ)
      ((regionBondConfigEquiv eY R).symm β) = _
  rw [Matrix.submatrix_mulVec_equiv]
  simp only [Function.comp_apply, Equiv.apply_symm_apply]
  rfl

/-- The actual global Fourier operation preserves every canonical parent
condition in an arbitrary family of regions. -/
theorem graphNumberedBondFamilyMatrix_oriented_coordinates_maps_regionParentGroundSpace
    {ι : Type*} (Q : Matrix Y X ℂ) (hQ : Q.conjTranspose * Q = 1)
    (U : G →* Matrix X X ℂ) (L : G →* Matrix Y Y ℂ)
    (hL : ∀ g, L g = Q * U g * Q.conjTranspose) (o : Edge Γ → Bool)
    (eX : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Y) ≃ Fin q) (R : ι → Finset V) :
    (regionParentGroundSpace (numberedGraphOrientedAveragingTensor U 1 o eX) R).map
      (Matrix.mulVecLin
        (graphNumberedBondFamilyMatrix eX eY (graphOrientedBondCoordinateMatrix Q o))) ≤
      regionParentGroundSpace (numberedGraphOrientedAveragingTensor L 1 o eY) R :=
  map_regionParentGroundSpace_le_of_blocks _ _ R _ fun i τ σ =>
    regionOperatorBlock_graphNumberedBondFamilyMatrix_oriented_coordinates_maps
      Q hQ U L hL o eX eY (R i) τ σ

omit [DecidableEq X] [Fintype Y] in
/-- The actual global Fourier map cancels against the inverse coordinate map
on every physical vector, not only on closed PEPS vectors. -/
theorem graphNumberedBondFamilyMatrix_oriented_coordinates_rightInverse [Finite Y]
    (Q : Matrix Y X ℂ) (hQ : Q * Q.conjTranspose = 1) (o : Edge Γ → Bool)
    (eX : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Y) ≃ Fin q)
    (ψ : (V → Fin q) → ℂ) :
    graphNumberedBondFamilyMatrix eX eY (graphOrientedBondCoordinateMatrix Q o) *ᵥ
      (graphNumberedBondFamilyMatrix eY eX
        (graphOrientedBondCoordinateMatrix Q.conjTranspose o) *ᵥ ψ) = ψ := by
  let := Fintype.ofFinite Y
  have he (e : Edge Γ) : graphOrientedBondCoordinateMatrix Q o e *
      graphOrientedBondCoordinateMatrix Q.conjTranspose o e = 1 := by
    unfold graphOrientedBondCoordinateMatrix graphOrientedEdgeCoordinateMatrix
    cases ho : o e
    · simp only [Bool.false_eq_true, ↓reduceIte, bondCoordinateMatrix_mul, hQ]
      exact bondCoordinateMatrix_one
    · simp only [↓reduceIte, bondCoordinateMatrix_mul,
        map_star_mul_eq_one Q Q.conjTranspose hQ]
      exact bondCoordinateMatrix_one
  rw [Matrix.mulVec_mulVec,
    graphNumberedBondFamilyMatrix_mul_eq_one eX eY _ _ he, Matrix.one_mulVec]

/-- Equality of the entire canonical parent ground spaces under the actual
Fourier operation. No coverage condition on the region family is needed. -/
theorem map_regionParentGroundSpace_oriented_coordinates_eq
    {ι : Type*} (Q : Matrix Y X ℂ) (hQ : Q.conjTranspose * Q = 1)
    (U : G →* Matrix X X ℂ) (L : G →* Matrix Y Y ℂ)
    (hL : ∀ g, L g = Q * U g * Q.conjTranspose) (o : Edge Γ → Bool)
    (eX : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Y) ≃ Fin q) (R : ι → Finset V) :
    (regionParentGroundSpace (numberedGraphOrientedAveragingTensor U 1 o eX) R).map
      (Matrix.mulVecLin
        (graphNumberedBondFamilyMatrix eX eY (graphOrientedBondCoordinateMatrix Q o))) =
      regionParentGroundSpace (numberedGraphOrientedAveragingTensor L 1 o eY) R := by
  apply le_antisymm
    (graphNumberedBondFamilyMatrix_oriented_coordinates_maps_regionParentGroundSpace
      Q hQ U L hL o eX eY R)
  intro ψ hψ
  have hQQ := mul_conjTranspose_eq_one_of_representation_coordinates Q U L hL
  have hinv : ∀ g, U g = Q.conjTranspose * L g * Q.conjTranspose.conjTranspose := by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      representation_coordinates_conjTranspose Q hQ U L hL
  refine ⟨graphNumberedBondFamilyMatrix eY eX
    (graphOrientedBondCoordinateMatrix Q.conjTranspose o) *ᵥ ψ,
    ?_, graphNumberedBondFamilyMatrix_oriented_coordinates_rightInverse Q hQQ o eX eY ψ⟩
  exact graphNumberedBondFamilyMatrix_oriented_coordinates_maps_regionParentGroundSpace
    Q.conjTranspose
    (by simpa only [Matrix.conjTranspose_conjTranspose] using hQQ) L U hinv o eY eX R
      ⟨ψ, hψ, rfl⟩

omit [DecidableEq Y] [Fintype X] in
/-- The Fourier bond matrix loses no physical vector. -/
theorem graphNumberedBondFamilyMatrix_oriented_coordinates_injective [Finite X]
    (Q : Matrix Y X ℂ) (hQ : Q.conjTranspose * Q = 1) (o : Edge Γ → Bool)
    (eX : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Y) ≃ Fin q) :
    Function.Injective (Matrix.mulVecLin
      (graphNumberedBondFamilyMatrix eX eY (graphOrientedBondCoordinateMatrix Q o))) := by
  let := Fintype.ofFinite X
  intro ψ φ h
  have hc (χ : (V → Fin p) → ℂ) :
      graphNumberedBondFamilyMatrix eY eX (graphOrientedBondCoordinateMatrix Q.conjTranspose o) *ᵥ
        (graphNumberedBondFamilyMatrix eX eY (graphOrientedBondCoordinateMatrix Q o) *ᵥ χ) = χ := by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      graphNumberedBondFamilyMatrix_oriented_coordinates_rightInverse Q.conjTranspose
        (by simpa only [Matrix.conjTranspose_conjTranspose] using hQ) o eY eX χ
  have he := congrArg (fun χ =>
    graphNumberedBondFamilyMatrix eY eX
      (graphOrientedBondCoordinateMatrix Q.conjTranspose o) *ᵥ χ) h
  change _ *ᵥ (_ *ᵥ ψ) = _ *ᵥ (_ *ᵥ φ) at he
  rwa [hc, hc] at he

/-- Restriction of the actual Fourier operation is a linear equivalence of
canonical parent ground spaces for every region family. -/
def canonicalOrientedCoordinateParentEquiv
    {ι : Type*} (Q : Matrix Y X ℂ) (hQ : Q.conjTranspose * Q = 1)
    (U : G →* Matrix X X ℂ) (L : G →* Matrix Y Y ℂ)
    (hL : ∀ g, L g = Q * U g * Q.conjTranspose) (o : Edge Γ → Bool)
    (eX : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Y) ≃ Fin q) (R : ι → Finset V) :
    regionParentGroundSpace (numberedGraphOrientedAveragingTensor U 1 o eX) R ≃ₗ[ℂ]
      regionParentGroundSpace (numberedGraphOrientedAveragingTensor L 1 o eY) R :=
  LinearEquiv.ofBijective
    (((Matrix.mulVecLin
        (graphNumberedBondFamilyMatrix eX eY (graphOrientedBondCoordinateMatrix Q o))) ∘ₗ
      (regionParentGroundSpace
        (numberedGraphOrientedAveragingTensor U 1 o eX) R).subtype).codRestrict
        _ (fun ψ =>
          graphNumberedBondFamilyMatrix_oriented_coordinates_maps_regionParentGroundSpace
            Q hQ U L hL o eX eY R ⟨ψ, ψ.2, rfl⟩))
    ⟨fun ψ φ h => Subtype.ext (graphNumberedBondFamilyMatrix_oriented_coordinates_injective
        Q hQ o eX eY
        (congrArg Subtype.val h)), by
      intro ψ
      have hψ := (map_regionParentGroundSpace_oriented_coordinates_eq Q hQ U L hL o eX eY R).ge ψ.2
      obtain ⟨φ, hφ, hEq⟩ := hψ
      exact ⟨⟨φ, hφ⟩, Subtype.ext hEq⟩⟩

/-- The dimension of the entire canonical parent kernel is coordinate invariant. -/
theorem finrank_regionParentGroundSpace_oriented_coordinates_eq
    {ι : Type*} (Q : Matrix Y X ℂ) (hQ : Q.conjTranspose * Q = 1)
    (U : G →* Matrix X X ℂ) (L : G →* Matrix Y Y ℂ)
    (hL : ∀ g, L g = Q * U g * Q.conjTranspose) (o : Edge Γ → Bool)
    (eX : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Y) ≃ Fin q) (R : ι → Finset V) :
    Module.finrank ℂ (regionParentGroundSpace (numberedGraphOrientedAveragingTensor L 1 o eY) R) =
      Module.finrank ℂ
        (regionParentGroundSpace (numberedGraphOrientedAveragingTensor U 1 o eX) R) :=
  (canonicalOrientedCoordinateParentEquiv Q hQ U L hL o eX eY R).symm.finrank_eq

/-- Fourier coordinates identify full kernels of arbitrary positive canonical
parent interactions, retaining their actual regional PEPS ranges. -/
theorem map_ker_regionParentHamiltonian_oriented_coordinates_eq
    {ι : Type*} [Fintype ι] (Q : Matrix Y X ℂ) (hQ : Q.conjTranspose * Q = 1)
    (U : G →* Matrix X X ℂ) (L : G →* Matrix Y Y ℂ)
    (hL : ∀ g, L g = Q * U g * Q.conjTranspose) (o : Edge Γ → Bool)
    (eX : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Y) ≃ Fin q) (R : ι → Finset V)
    (H : (i : ι) → Matrix (RegionPhysicalConfig (d := p) (R i))
      (RegionPhysicalConfig (d := p) (R i)) ℂ)
    (K : (i : ι) → Matrix (RegionPhysicalConfig (d := q) (R i))
      (RegionPhysicalConfig (d := q) (R i)) ℂ)
    (hH : ∀ i, IsRegionParentInteraction (numberedGraphOrientedAveragingTensor U 1 o eX)
      (R i) (H i))
    (hK : ∀ i, IsRegionParentInteraction (numberedGraphOrientedAveragingTensor L 1 o eY)
      (R i) (K i)) :
    (Matrix.mulVecLin (regionParentHamiltonian R H)).ker.map
      (Matrix.mulVecLin
        (graphNumberedBondFamilyMatrix eX eY (graphOrientedBondCoordinateMatrix Q o))) =
      (Matrix.mulVecLin (regionParentHamiltonian R K)).ker := by
  rw [ker_regionParentHamiltonian _ R H hH, ker_regionParentHamiltonian _ R K hK]
  exact map_regionParentGroundSpace_oriented_coordinates_eq Q hQ U L hL o eX eY R

end TNLean.PEPS

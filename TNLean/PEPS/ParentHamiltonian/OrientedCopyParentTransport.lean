/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GraphOrientedCopyTransport
import TNLean.PEPS.GraphOrientedBondRangeSupport
import TNLean.PEPS.ParentHamiltonian.CopyCanonicalLocalTransport
import TNLean.PEPS.ParentHamiltonian.GraphBondPhysicalCoordinates
import TNLean.PEPS.SemiRegularBondRetraction

/-!
# Canonical parent equivalence for arbitrarily oriented copy restoration

Actual open-region contractions prove both range inclusions, and edge-covering
parent conditions derive both required product supports. The fixed physical
bond map therefore identifies every canonical parent ground vector for arbitrary
positive copy counts and arbitrary native edge orientations.

Source: SCP10, arXiv:1001.3807, Theorem 5.7 and Section 7, lines 2977–3019.
-/

noncomputable section
open scoped Matrix BigOperators Kronecker
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
private abbrev RB (R : Finset V) := {e : Edge Γ // IsRegionBoundaryEdge R e}
variable {p q : ℕ}
variable {G I : Type*} [Group G] [Fintype G] [Fintype I] [DecidableEq I]

/-- The explicit open-generator formula gives a local-range inclusion in
bond coordinates. -/
theorem graphRegionCopyMatrix_maps_oriented_openBondSpace
    (o : Edge Γ → Bool) (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i) (R : Finset V)
    (γ : RB (Γ := Γ) R → Σ i, Fin (d i) × Fin (m i)) :
    (graphOrientedOpenBondSpace (blockMatrixRepresentation d D)
        (blockMultiplicityRootWeight d m) o R).map
      (Matrix.mulVecLin (graphRegionCopyMatrix d m R γ)) ≤
      graphOrientedOpenBondSpace (blockMultiplicityRepresentation d m D) 1 o R := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro _ ⟨θ, rfl⟩
  change graphRegionCopyMatrix d m R γ *ᵥ
    graphOrientedOpenBondCoordinates (blockMatrixRepresentation d D)
      (blockMultiplicityRootWeight d m) o R θ ∈
      graphOrientedOpenBondSpace (blockMultiplicityRepresentation d m D) 1 o R
  rw [graphRegionCopyMatrix_oriented_open o d m D hm]
  apply Submodule.sum_smul_mem
  intro a _
  exact Submodule.subset_span ⟨a, rfl⟩

/-- The explicit adjoint boundary formula gives the opposite local-range
inclusion, without requiring ambient physical surjectivity. -/
theorem graphRegionCopyMatrix_adjoint_maps_oriented_openBondSpace
    (o : Edge Γ → Bool) (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i) (R : Finset V)
    (γ : RB (Γ := Γ) R → Σ i, Fin (d i) × Fin (m i)) :
    (graphOrientedOpenBondSpace (blockMultiplicityRepresentation d m D) 1 o R).map
      (Matrix.mulVecLin (graphRegionCopyMatrix d m R γ).conjTranspose) ≤
      graphOrientedOpenBondSpace (blockMatrixRepresentation d D)
        (blockMultiplicityRootWeight d m) o R := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro _ ⟨θ, rfl⟩
  change (graphRegionCopyMatrix d m R γ).conjTranspose *ᵥ
    graphOrientedOpenBondCoordinates (blockMultiplicityRepresentation d m D) 1 o R θ ∈
      graphOrientedOpenBondSpace (blockMatrixRepresentation d D)
        (blockMultiplicityRootWeight d m) o R
  rw [graphRegionCopyMatrix_adjoint_oriented_open o d m D hm]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- The actual numbered regional spaces are carried forward by the explicit
regional multiplicity matrix. -/
theorem numberedRegionCopyMatrix_maps_oriented_regionGroundSpace
    (o : Edge Γ → Bool) (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (m i)) ≃ Fin q)
    (R : Finset V) (γ : RB (Γ := Γ) R → Σ i, Fin (d i) × Fin (m i)) :
    (regionGroundSpace (numberedGraphOrientedAveragingTensor
      (blockMatrixRepresentation d D) (blockMultiplicityRootWeight d m) o eX) R).map
      (Matrix.mulVecLin (numberedRegionCopyMatrix d m eX eY R γ)) ≤
      regionGroundSpace (numberedGraphOrientedAveragingTensor
        (blockMultiplicityRepresentation d m D) 1 o eY) R := by
  rintro _ ⟨ψ, hψ, rfl⟩
  apply (regionBondPhysicalEquiv_mem_graphOrientedOpenBondSpace_iff _ _
    (fun g => Commute.one_left _) o eY R _).mp
  have hs := (regionBondPhysicalEquiv_mem_graphOrientedOpenBondSpace_iff _ _
    (blockMultiplicityRootWeight_commute d m D) o eX R ψ).mpr hψ
  have ht := graphRegionCopyMatrix_maps_oriented_openBondSpace o d m D hm R γ
    ⟨regionBondPhysicalEquiv eX R ψ, hs, rfl⟩
  convert ht using 1
  funext β
  change (numberedRegionCopyMatrix d m eX eY R γ *ᵥ ψ)
    ((regionBondConfigEquiv eY R).symm β) = _
  rw [numberedRegionCopyMatrix, Matrix.submatrix_mulVec_equiv]
  simp only [Function.comp_apply, Equiv.apply_symm_apply]
  rfl

/-- The adjoint numbered matrix carries the actual repeated regional range
back into the actual weighted regional range. -/
theorem numberedRegionCopyMatrix_adjoint_maps_oriented_regionGroundSpace
    (o : Edge Γ → Bool) (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (m i)) ≃ Fin q)
    (R : Finset V) (γ : RB (Γ := Γ) R → Σ i, Fin (d i) × Fin (m i)) :
    (regionGroundSpace (numberedGraphOrientedAveragingTensor
      (blockMultiplicityRepresentation d m D) 1 o eY) R).map
      (Matrix.mulVecLin (numberedRegionCopyMatrix d m eX eY R γ).conjTranspose) ≤
      regionGroundSpace (numberedGraphOrientedAveragingTensor
        (blockMatrixRepresentation d D) (blockMultiplicityRootWeight d m) o eX) R := by
  rintro _ ⟨ψ, hψ, rfl⟩
  apply (regionBondPhysicalEquiv_mem_graphOrientedOpenBondSpace_iff _ _
    (blockMultiplicityRootWeight_commute d m D) o eX R _).mp
  have hs := (regionBondPhysicalEquiv_mem_graphOrientedOpenBondSpace_iff _ _
    (fun g => Commute.one_left _) o eY R ψ).mpr hψ
  have ht := graphRegionCopyMatrix_adjoint_maps_oriented_openBondSpace o d m D hm R γ
    ⟨regionBondPhysicalEquiv eY R ψ, hs, rfl⟩
  convert ht using 1
  funext β
  change ((numberedRegionCopyMatrix d m eX eY R γ).conjTranspose *ᵥ ψ)
    ((regionBondConfigEquiv eX R).symm β) = _
  rw [numberedRegionCopyMatrix, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mulVec_equiv]
  simp only [Function.comp_apply, Equiv.apply_symm_apply]
  rfl

/-- Every actual canonical parent condition is preserved by the global
supported multiplicity-restoring matrix. No coverage is needed for inclusion. -/
theorem graphNumberedCopyMatrix_maps_oriented_parent
    (o : Edge Γ → Bool) (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (m i)) ≃ Fin q)
    {ι : Type*} (R : ι → Finset V) :
    (regionParentGroundSpace (numberedGraphOrientedAveragingTensor
      (blockMatrixRepresentation d D) (blockMultiplicityRootWeight d m) o eX) R).map
      (Matrix.mulVecLin (graphNumberedBondMatrix eX eY
        (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (m i))))) ≤
      regionParentGroundSpace (numberedGraphOrientedAveragingTensor
        (blockMultiplicityRepresentation d m D) 1 o eY) R := by
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
    (numberedRegionCopyMatrix_maps_oriented_regionGroundSpace o d m D hm eX eY (R i) _
      ⟨φ, hφ, rfl⟩)

/-- The global adjoint preserves the opposite actual canonical parent conditions. -/
theorem graphNumberedCopyMatrix_adjoint_maps_oriented_parent
    (o : Edge Γ → Bool) (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (m i)) ≃ Fin q)
    {ι : Type*} (R : ι → Finset V) :
    (regionParentGroundSpace (numberedGraphOrientedAveragingTensor
      (blockMultiplicityRepresentation d m D) 1 o eY) R).map
      (Matrix.mulVecLin (graphNumberedBondMatrix eX eY
        (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (m i)))).conjTranspose) ≤
      regionParentGroundSpace (numberedGraphOrientedAveragingTensor
        (blockMatrixRepresentation d D) (blockMultiplicityRootWeight d m) o eX) R := by
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
    (numberedRegionCopyMatrix_adjoint_maps_oriented_regionGroundSpace o d m D hm eX eY (R i) _
      ⟨φ, hφ, rfl⟩)

/-- Canonical source parent constraints supply the full support required to
recover every source ground vector by the global adjoint. -/
theorem graphNumberedCopyMatrix_leftInverse_oriented_parent
    (o : Edge Γ → Bool) (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (m i)) ≃ Fin q)
    {ι : Type*} (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i)
    {ψ : (V → Fin p) → ℂ}
    (hψ : ψ ∈ regionParentGroundSpace (numberedGraphOrientedAveragingTensor
      (blockMatrixRepresentation d D) (blockMultiplicityRootWeight d m) o eX) R) :
    let M := graphNumberedBondMatrix eX eY
      (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (m i)))
    M.conjTranspose *ᵥ (M *ᵥ ψ) = ψ := by
  let : ∀ i, Nonempty (Fin (m i)) := fun i => ⟨⟨0, hm i⟩⟩
  apply (graphBondPhysicalEquiv eX).injective
  rw [graphNumberedBondMatrix_conjTranspose, graphBondPhysicalEquiv_mulVec,
    graphBondPhysicalEquiv_mulVec]
  apply physicalProductMap_fullMultiplicityBondMap_leftInverse
  apply regionParentGroundSpace_mem_product_range_of_oriented_factors
    (blockMatrixRepresentation d D) (blockMultiplicityRootWeight d m)
    (blockMultiplicityRootWeight_commute d m D) o
    (blockBondInclusion (fun i => Fin (d i))) _ _ eX R hcover hψ
  · intro g
    rw [blockMultiplicityRootWeight_sq_mul]
    exact ⟨_, blockBondInclusion_mulVec (fun i => Fin (d i))
      (fun i => (Real.sqrt (m i : ℝ) : ℂ) • D i g)⟩
  · intro g
    rw [blockMultiplicityRootWeight_sq_mul]
    refine ⟨fun c => ((Real.sqrt (m c.1 : ℝ) : ℂ) • D c.1 g) c.2.2 c.2.1, ?_⟩
    simpa only [Matrix.mulVecLin_apply, ← Matrix.blockDiagonal'_transpose,
      Matrix.transpose_apply] using
      blockBondInclusion_mulVec (fun i => Fin (d i))
        (fun i => ((Real.sqrt (m i : ℝ) : ℂ) • D i g).transpose)

/-- Target canonical parent constraints supply the entire output support,
so the global map recovers every target ground vector from its adjoint image. -/
theorem graphNumberedCopyMatrix_rightInverse_oriented_parent
    (o : Edge Γ → Bool) (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (m i)) ≃ Fin q)
    {ι : Type*} (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i)
    {ψ : (V → Fin q) → ℂ}
    (hψ : ψ ∈ regionParentGroundSpace (numberedGraphOrientedAveragingTensor
      (blockMultiplicityRepresentation d m D) 1 o eY) R) :
    let M := graphNumberedBondMatrix eX eY
      (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (m i)))
    M *ᵥ (M.conjTranspose *ᵥ ψ) = ψ := by
  let : ∀ i, Nonempty (Fin (m i)) := fun i => ⟨⟨0, hm i⟩⟩
  apply (graphBondPhysicalEquiv eY).injective
  rw [graphBondPhysicalEquiv_mulVec, graphNumberedBondMatrix_conjTranspose,
    graphBondPhysicalEquiv_mulVec]
  apply physicalProductMap_fullMultiplicityBondMap_rightInverse
  apply regionParentGroundSpace_mem_product_range_of_oriented_factors
    (blockMultiplicityRepresentation d m D) 1 (fun _ => Commute.one_left _) o
    (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (m i))) _ _ eY R hcover hψ
  · intro g
    refine ⟨fun r => Matrix.blockDiagonal'
      (fun i => (Real.sqrt (m i : ℝ) : ℂ) • D i g) r.1 r.2, ?_⟩
    simpa [blockMultiplicityRepresentation] using
      fullMultiplicityBondMap_mulVec_sqrt_blockDiagonal
        (fun i => Fin (d i)) (fun i => Fin (m i)) (fun i => D i g)
  · intro g
    refine ⟨fun r => Matrix.blockDiagonal'
      (fun i => (Real.sqrt (m i : ℝ) : ℂ) • D i g) r.2 r.1, ?_⟩
    simpa [blockMultiplicityRepresentation] using
      fullMultiplicityBondMap_mulVec_sqrt_blockDiagonal_transpose
        (fun i => Fin (d i)) (fun i => Fin (m i)) (fun i => D i g)

/-- Multiplicity restoration identifies the entire actual canonical parent
spaces whenever the chosen regions contain every edge. -/
theorem map_regionParentGroundSpace_oriented_copy_eq
    (o : Edge Γ → Bool) (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (m i)) ≃ Fin q)
    {ι : Type*} (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i) :
    (regionParentGroundSpace (numberedGraphOrientedAveragingTensor
      (blockMatrixRepresentation d D) (blockMultiplicityRootWeight d m) o eX) R).map
      (Matrix.mulVecLin (graphNumberedBondMatrix eX eY
        (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (m i))))) =
      regionParentGroundSpace (numberedGraphOrientedAveragingTensor
        (blockMultiplicityRepresentation d m D) 1 o eY) R := by
  apply le_antisymm (graphNumberedCopyMatrix_maps_oriented_parent o d m D hm eX eY R)
  intro ψ hψ
  refine ⟨(graphNumberedBondMatrix eX eY
    (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (m i)))).conjTranspose *ᵥ ψ,
    ?_, graphNumberedCopyMatrix_rightInverse_oriented_parent o d m D hm eX eY R hcover hψ⟩
  exact graphNumberedCopyMatrix_adjoint_maps_oriented_parent o d m D hm eX eY R ⟨ψ, hψ, rfl⟩

/-- The physical bond map loses no source canonical parent ground vector. -/
theorem graphNumberedCopyMatrix_injOn_oriented_parent
    (o : Edge Γ → Bool) (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (m i)) ≃ Fin q)
    {ι : Type*} (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i) :
    Set.InjOn (Matrix.mulVecLin (graphNumberedBondMatrix eX eY
      (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (m i)))))
      (regionParentGroundSpace (numberedGraphOrientedAveragingTensor
        (blockMatrixRepresentation d D) (blockMultiplicityRootWeight d m) o eX) R) := by
  intro ψ hψ φ hφ hEq
  have h := congrArg (fun x => (graphNumberedBondMatrix eX eY
    (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (m i)))).conjTranspose *ᵥ x) hEq
  change _ *ᵥ (_ *ᵥ ψ) = _ *ᵥ (_ *ᵥ φ) at h
  rwa [graphNumberedCopyMatrix_leftInverse_oriented_parent o d m D hm eX eY R hcover hψ,
    graphNumberedCopyMatrix_leftInverse_oriented_parent o d m D hm eX eY R hcover hφ] at h

/-- Restriction of the actual supported bond map gives a linear equivalence
of the entire canonical parent ground spaces. -/
def canonicalOrientedCopyParentEquiv
    (o : Edge Γ → Bool) (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (m i)) ≃ Fin q)
    {ι : Type*} (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i) :
    regionParentGroundSpace (numberedGraphOrientedAveragingTensor
      (blockMatrixRepresentation d D) (blockMultiplicityRootWeight d m) o eX) R ≃ₗ[ℂ]
      regionParentGroundSpace (numberedGraphOrientedAveragingTensor
        (blockMultiplicityRepresentation d m D) 1 o eY) R :=
  LinearEquiv.ofBijective
    (((Matrix.mulVecLin (graphNumberedBondMatrix eX eY
      (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (m i))))) ∘ₗ
      (regionParentGroundSpace (numberedGraphOrientedAveragingTensor
        (blockMatrixRepresentation d D)
          (blockMultiplicityRootWeight d m) o eX) R).subtype).codRestrict _
      (fun ψ => graphNumberedCopyMatrix_maps_oriented_parent o d m D hm eX eY R ⟨ψ, ψ.2, rfl⟩))
    ⟨fun ψ φ h => Subtype.ext (graphNumberedCopyMatrix_injOn_oriented_parent
        o d m D hm eX eY R hcover ψ.2 φ.2 (congrArg Subtype.val h)), by
      intro ψ
      have hψ := (map_regionParentGroundSpace_oriented_copy_eq o d m D hm eX eY R hcover).ge ψ.2
      obtain ⟨φ, hφ, hEq⟩ := hψ
      exact ⟨⟨φ, hφ⟩, Subtype.ext hEq⟩⟩

/-- The full canonical ground-space dimension is unchanged by multiplicity restoration. -/
theorem finrank_regionParentGroundSpace_oriented_copy_eq
    (o : Edge Γ → Bool) (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (m i)) ≃ Fin q)
    {ι : Type*} (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i) :
    Module.finrank ℂ (regionParentGroundSpace (numberedGraphOrientedAveragingTensor
      (blockMultiplicityRepresentation d m D) 1 o eY) R) =
      Module.finrank ℂ (regionParentGroundSpace (numberedGraphOrientedAveragingTensor
        (blockMatrixRepresentation d D) (blockMultiplicityRootWeight d m) o eX) R) :=
  (canonicalOrientedCopyParentEquiv o d m D hm eX eY R hcover).symm.finrank_eq

/-- Arbitrary positive canonical parent interactions, with the actual regional
kernels on both sides, have their full Hamiltonian kernels identified by the
physical bond map. The conclusion concerns every ground vector. -/
theorem map_ker_regionParentHamiltonian_oriented_copy_eq
    (o : Edge Γ → Bool) (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (m i)) ≃ Fin q)
    {ι : Type*} [Fintype ι] (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i)
    (H : (i : ι) → Matrix (RegionPhysicalConfig (d := p) (R i))
      (RegionPhysicalConfig (d := p) (R i)) ℂ)
    (K : (i : ι) → Matrix (RegionPhysicalConfig (d := q) (R i))
      (RegionPhysicalConfig (d := q) (R i)) ℂ)
    (hH : ∀ i, IsRegionParentInteraction (numberedGraphOrientedAveragingTensor
      (blockMatrixRepresentation d D) (blockMultiplicityRootWeight d m) o eX) (R i) (H i))
    (hK : ∀ i, IsRegionParentInteraction (numberedGraphOrientedAveragingTensor
      (blockMultiplicityRepresentation d m D) 1 o eY) (R i) (K i)) :
    (Matrix.mulVecLin (regionParentHamiltonian R H)).ker.map
      (Matrix.mulVecLin (graphNumberedBondMatrix eX eY
        (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (m i))))) =
      (Matrix.mulVecLin (regionParentHamiltonian R K)).ker := by
  rw [ker_regionParentHamiltonian _ R H hH, ker_regionParentHamiltonian _ R K hK]
  exact map_regionParentGroundSpace_oriented_copy_eq o d m D hm eX eY R hcover

end TNLean.PEPS

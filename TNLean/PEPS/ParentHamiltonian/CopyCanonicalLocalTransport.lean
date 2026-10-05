/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.GraphCanonicalBondCoordinates
import TNLean.PEPS.GraphOpenCopyTransport

/-!
# Canonical local-range transport for arbitrary positive copy counts

The internal and crossing maps, and their adjoints, preserve the actual
canonical regional conditions when the target repeats each block mᵢ times.
The single-copy source is weighted by mᵢ^(1/4), independently of dᵢ.

Source: SCP10, arXiv:1001.3807, Theorem 5.7 and the copy-restoring
bond map of Section 7, lines 2977–3019.
-/

noncomputable section
open scoped Matrix BigOperators
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
private abbrev RI (R : Finset V) := {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}
private abbrev RB (R : Finset V) := {e : Edge Γ // IsRegionBoundaryEdge R e}
variable {G : Type*} [Group G] [Fintype G] {p q : ℕ}

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The regional multiplicity map in numbered physical coordinates. -/
def numberedRegionCopyMatrix (d m : I → ℕ)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (m i)) ≃ Fin q)
    (R : Finset V) (γ : RB (Γ := Γ) R → Σ i, Fin (d i) × Fin (m i)) :
    Matrix (RegionPhysicalConfig (d := q) R) (RegionPhysicalConfig (d := p) R) ℂ :=
  (graphRegionCopyMatrix d m R γ).submatrix
    (regionBondConfigEquiv eY R) (regionBondConfigEquiv eX R)

/-- The explicit open-generator formula gives a local-range inclusion in
bond coordinates. -/
theorem graphRegionCopyMatrix_maps_openBondSpace
    (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i) (R : Finset V)
    (γ : RB (Γ := Γ) R → Σ i, Fin (d i) × Fin (m i)) :
    (graphOpenBondSpace (blockMatrixRepresentation d D) (blockMultiplicityRootWeight d m) R).map
      (Matrix.mulVecLin (graphRegionCopyMatrix d m R γ)) ≤
      graphOpenBondSpace (blockMultiplicityRepresentation d m D) 1 R := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro _ ⟨θ, rfl⟩
  change graphRegionCopyMatrix d m R γ *ᵥ
    graphOpenBondCoordinates (blockMatrixRepresentation d D) (blockMultiplicityRootWeight d m) R θ ∈
      graphOpenBondSpace (blockMultiplicityRepresentation d m D) 1 R
  rw [graphRegionCopyMatrix_open d m D hm]
  apply Submodule.sum_smul_mem
  intro a _
  exact Submodule.subset_span ⟨a, rfl⟩

/-- The explicit adjoint boundary formula gives the opposite local-range
inclusion, without requiring ambient physical surjectivity. -/
theorem graphRegionCopyMatrix_adjoint_maps_openBondSpace
    (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i) (R : Finset V)
    (γ : RB (Γ := Γ) R → Σ i, Fin (d i) × Fin (m i)) :
    (graphOpenBondSpace (blockMultiplicityRepresentation d m D) 1 R).map
      (Matrix.mulVecLin (graphRegionCopyMatrix d m R γ).conjTranspose) ≤
      graphOpenBondSpace (blockMatrixRepresentation d D) (blockMultiplicityRootWeight d m) R := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro _ ⟨θ, rfl⟩
  change (graphRegionCopyMatrix d m R γ).conjTranspose *ᵥ
    graphOpenBondCoordinates (blockMultiplicityRepresentation d m D) 1 R θ ∈
      graphOpenBondSpace (blockMatrixRepresentation d D) (blockMultiplicityRootWeight d m) R
  rw [graphRegionCopyMatrix_adjoint_open d m D hm]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- The actual numbered regional spaces are carried forward by the explicit
regional multiplicity matrix. -/
theorem numberedRegionCopyMatrix_maps_regionGroundSpace
    (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (m i)) ≃ Fin q)
    (R : Finset V) (γ : RB (Γ := Γ) R → Σ i, Fin (d i) × Fin (m i)) :
    (regionGroundSpace (numberedGraphDressedAveragingTensor
      (blockMatrixRepresentation d D) (blockMultiplicityRootWeight d m) eX) R).map
      (Matrix.mulVecLin (numberedRegionCopyMatrix d m eX eY R γ)) ≤
      regionGroundSpace (numberedGraphDressedAveragingTensor
        (blockMultiplicityRepresentation d m D) 1 eY) R := by
  rintro _ ⟨ψ, hψ, rfl⟩
  apply (regionBondPhysicalEquiv_mem_graphOpenBondSpace_iff _ _
    (fun g => Commute.one_left _) eY R _).mp
  have hs := (regionBondPhysicalEquiv_mem_graphOpenBondSpace_iff _ _
    (blockMultiplicityRootWeight_commute d m D) eX R ψ).mpr hψ
  have ht := graphRegionCopyMatrix_maps_openBondSpace d m D hm R γ
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
theorem numberedRegionCopyMatrix_adjoint_maps_regionGroundSpace
    (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (m i)) ≃ Fin q)
    (R : Finset V) (γ : RB (Γ := Γ) R → Σ i, Fin (d i) × Fin (m i)) :
    (regionGroundSpace (numberedGraphDressedAveragingTensor
      (blockMultiplicityRepresentation d m D) 1 eY) R).map
      (Matrix.mulVecLin (numberedRegionCopyMatrix d m eX eY R γ).conjTranspose) ≤
      regionGroundSpace (numberedGraphDressedAveragingTensor
        (blockMatrixRepresentation d D) (blockMultiplicityRootWeight d m) eX) R := by
  rintro _ ⟨ψ, hψ, rfl⟩
  apply (regionBondPhysicalEquiv_mem_graphOpenBondSpace_iff _ _
    (blockMultiplicityRootWeight_commute d m D) eX R _).mp
  have hs := (regionBondPhysicalEquiv_mem_graphOpenBondSpace_iff _ _
    (fun g => Commute.one_left _) eY R ψ).mpr hψ
  have ht := graphRegionCopyMatrix_adjoint_maps_openBondSpace d m D hm R γ
    ⟨regionBondPhysicalEquiv eY R ψ, hs, rfl⟩
  convert ht using 1
  funext β
  change ((numberedRegionCopyMatrix d m eX eY R γ).conjTranspose *ᵥ ψ)
    ((regionBondConfigEquiv eX R).symm β) = _
  rw [numberedRegionCopyMatrix, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mulVec_equiv]
  simp only [Function.comp_apply, Equiv.apply_symm_apply]
  rfl

end TNLean.PEPS

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.PhysicalMapInjectivity
import TNLean.MPS.Symmetry.ProjectiveAdjointAction
import TNLean.MPS.Core.PhysicalRotation

/-!
# Physical coefficients and virtual covariance

The column action on the physical coefficient matrix is the transpose of
left multiplication on virtual matrices, tensored with right multiplication.
This records the row convention in the symmetric polar deformation of
Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.D.2.
-/

open scoped Matrix Kronecker MatrixOrder ComplexOrder

namespace MPSTensor

/-- The right action on the virtual-pair columns that corresponds to
`M ↦ X * M * Y`. Source: arXiv:1010.3732, Section II.D.2. -/
noncomputable def virtualPairRightAction {D : ℕ}
    (X Y : Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  Xᵀ ⊗ₖ Y

/-- Multiplying the physical coefficient matrix on the right by the pair
action conjugates each virtual matrix on the left and right.
Source: arXiv:1010.3732, Section II.D.2. -/
theorem physicalCoefficientMatrix_mul_virtualPairRightAction
    {d D : ℕ} (A : MPSTensor d D)
    (X Y : Matrix (Fin D) (Fin D) ℂ) :
    physicalCoefficientMatrix A * virtualPairRightAction X Y =
      physicalCoefficientMatrix (fun i ↦ X * A i * Y) := by
  classical
  ext i ⟨a, b⟩
  simp only [Matrix.mul_apply, virtualPairRightAction,
    Matrix.kroneckerMap_apply, Matrix.transpose_apply,
    physicalCoefficientMatrix]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  ring

/-- Physical rotation and exact virtual left-right covariance are
equivalent to an intertwining identity for the coefficient matrix.
Source: arXiv:1010.3732, Section II.D.2. -/
theorem physicalCoefficientMatrix_intertwining_iff_covariance
    {d D : ℕ} (A : MPSTensor d D)
    (U : Matrix (Fin d) (Fin d) ℂ)
    (X Y : Matrix (Fin D) (Fin D) ℂ) :
    U * physicalCoefficientMatrix A =
        physicalCoefficientMatrix A * virtualPairRightAction X Y ↔
      rotatePhysical U A = fun i ↦ X * A i * Y := by
  rw [physicalCoefficientMatrix_mul_virtualPairRightAction]
  constructor
  · intro h
    funext i a b
    have hij := congrArg (fun M : Matrix (Fin d) (Fin D × Fin D) ℂ ↦ M i (a, b)) h
    simpa [Matrix.mul_apply, physicalCoefficientMatrix, rotatePhysical,
      Matrix.sum_apply] using hij
  · intro h
    ext i ⟨a, b⟩
    have hij := congrArg (fun T : MPSTensor d D ↦ T i a b) h
    simpa [Matrix.mul_apply, physicalCoefficientMatrix, rotatePhysical,
      Matrix.sum_apply] using hij

/-- The pair-column action of a projective virtual representation, using
the inverse group element required by the physical row convention.
Source: arXiv:1010.3732, Section II.F.2. -/
noncomputable def virtualPairRightActionOfProjective
    {G : Type*} [Group G] {D : ℕ} {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ : TNLean.Algebra.ProjectiveRepresentation (D := D) ω) (g : G) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  virtualPairRightAction (ρ.X g⁻¹ : Matrix (Fin D) (Fin D) ℂ)
    (((ρ.X g⁻¹)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)

/-- Unitary virtual matrices induce unitary pair-column actions.
Source: arXiv:1010.3732, Section II.F.2. -/
theorem virtualPairRightActionOfProjective_mem_unitaryGroup
    {G : Type*} [Group G] {D : ℕ} {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ : TNLean.Algebra.ProjectiveRepresentation (D := D) ω)
    (hρ : ∀ g : G, (ρ.X g : Matrix (Fin D) (Fin D) ℂ) ∈
      Matrix.unitaryGroup (Fin D) ℂ) (g : G) :
    virtualPairRightActionOfProjective ρ g ∈
      Matrix.unitaryGroup (Fin D × Fin D) ℂ := by
  unfold virtualPairRightActionOfProjective virtualPairRightAction
  apply Matrix.kronecker_mem_unitary
  · exact Matrix.transpose_mem_unitaryGroup_iff.mpr (hρ g⁻¹)
  · let X := ρ.X g⁻¹
    have hInv : ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) =
        star (X : Matrix (Fin D) (Fin D) ℂ) := by
      let Q : Matrix.unitaryGroup (Fin D) ℂ := ⟨X.val, hρ g⁻¹⟩
      have hQ : Unitary.toUnits Q = X := Units.ext rfl
      rw [← hQ]
      rfl
    change ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) ∈
      Matrix.unitaryGroup (Fin D) ℂ
    rw [hInv]
    exact Unitary.star_mem (hρ g⁻¹)

/-- An injective tensor with unitary virtual projective symmetry admits a
continuous polar deformation through injective tensors with the same exact
virtual covariance. The covariance is expressed by gauge equivalence at
each parameter. Source: Schuch–Pérez-García–Cirac,
arXiv:1010.3732, Section II.D.2, equation following
`eq:1d-iso:polardec`, and Section II.F.2. -/
theorem exists_projective_equivariant_polar_tensor_path
    {G : Type*} [Group G] {d D : ℕ}
    {ω : TNLean.Algebra.ScalarCocycle G}
    (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (ρ : TNLean.Algebra.ProjectiveRepresentation (D := D) ω)
    (U : G → Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hρ : ∀ g : G, (ρ.X g : Matrix (Fin D) (Fin D) ℂ) ∈
      Matrix.unitaryGroup (Fin D) ℂ)
    (hCov : ∀ g, rotatePhysical (U g) A =
      fun i ↦ (ρ.X g⁻¹ : Matrix (Fin D) (Fin D) ℂ) * A i *
        (((ρ.X g⁻¹)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) :
    ∃ (Q : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)
      (W : Matrix (Fin d) (Fin D × Fin D) ℂ),
      Q.PosDef ∧ Wᴴ * W = 1 ∧
      A = tensorOfPhysicalCoefficientMatrix (W * Matrix.polarInterpolant Q 1) ∧
      (∀ γ : ℝ, 0 ≤ γ → γ ≤ 1 →
        Kraus.IsInjective
          (tensorOfPhysicalCoefficientMatrix (W * Matrix.polarInterpolant Q γ))) ∧
      Continuous (fun γ : ℝ ↦
        tensorOfPhysicalCoefficientMatrix (W * Matrix.polarInterpolant Q γ)) ∧
      (∀ γ : ℝ, ∀ g : G,
        GaugeEquiv
          (tensorOfPhysicalCoefficientMatrix (W * Matrix.polarInterpolant Q γ))
          (rotatePhysical (U g)
            (tensorOfPhysicalCoefficientMatrix (W * Matrix.polarInterpolant Q γ)))) := by
  let R : G → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
    virtualPairRightActionOfProjective ρ
  have hInter : ∀ g, U g * physicalCoefficientMatrix A =
      physicalCoefficientMatrix A * R g := by
    intro g
    exact (physicalCoefficientMatrix_intertwining_iff_covariance A (U g)
      (ρ.X g⁻¹ : Matrix (Fin D) (Fin D) ℂ)
      (((ρ.X g⁻¹)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)).2 (hCov g)
  obtain ⟨Q, W, hQ, hW, hPend, _, _, hcont, _, hInterPath⟩ :=
    Matrix.exists_equivariant_polar_deformation_of_injective
      (physicalCoefficientMatrix A)
      (physicalCoefficientMatrix_mulVec_injective_of_isInjective A hA)
      U R hU (virtualPairRightActionOfProjective_mem_unitaryGroup ρ hρ) hInter
  refine ⟨Q, W, hQ, hW, ?_, ?_, ?_, ?_⟩
  · simpa only [← hPend] using
      (show A = tensorOfPhysicalCoefficientMatrix (physicalCoefficientMatrix A) from rfl)
  · intro γ hγ₀ hγ₁
    exact isInjective_tensorOf_isometric_polarInterpolant hW hQ hγ₀ hγ₁
  · apply continuous_pi
    intro i
    apply continuous_matrix
    intro a b
    exact hcont.matrix_elem i (a, b)
  · intro γ g
    refine ⟨ρ.X g⁻¹, ?_⟩
    have hPath := hInterPath g γ
    have hExact := (physicalCoefficientMatrix_intertwining_iff_covariance
      (tensorOfPhysicalCoefficientMatrix (W * Matrix.polarInterpolant Q γ))
      (U g)
      (ρ.X g⁻¹ : Matrix (Fin D) (Fin D) ℂ)
      (((ρ.X g⁻¹)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)).1 ?_
    · exact congrFun hExact
    · simpa only [physicalCoefficientMatrix_tensorOfPhysicalCoefficientMatrix,
        R, virtualPairRightActionOfProjective] using hPath

end MPSTensor

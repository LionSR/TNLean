/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CocycleCohomology
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.UnitaryGroup
import QICLean.Algebra.MatrixReindexUnitary

/-!
# Linear action induced by a virtual projective representation

The virtual action on the two ends of a maximally entangled bond is linear:
the scalar multiplier of a projective representation cancels in conjugation.
This is the algebraic content of the physical action `V_g ⊗ \bar V_g` in
Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.F.2, lines 839–929.
-/

open scoped Matrix Kronecker
open Module

namespace TNLean.Algebra

variable {G : Type*} [Group G] {D : ℕ} {ω : ScalarCocycle G}

/-- The adjoint action of a virtual projective matrix on the bond matrix
algebra. -/
def ProjectiveRepresentation.adjoint (ρ : ProjectiveRepresentation (D := D) ω)
    (g : G) (M : Matrix (Fin D) (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  (ρ.X g : Matrix (Fin D) (Fin D) ℂ) * M *
    (((ρ.X g)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)

private theorem scalar_mul_adjoint (u : Units ℂ)
    (X : GL (Fin D) ℂ) (M : Matrix (Fin D) (Fin D) ℂ) :
    (Matrix.GeneralLinearGroup.scalar (Fin D) u * X).val * M *
      ((Matrix.GeneralLinearGroup.scalar (Fin D) u * X)⁻¹).val =
    X.val * M * (X⁻¹).val := by
  rw [mul_inv_rev, ← map_inv (Matrix.GeneralLinearGroup.scalar (Fin D)) u]
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul,
    ← Matrix.smul_eq_mul_diagonal,
    Units.val_inv_eq_inv_val]
  simp [Matrix.mul_assoc]

/-- The adjoint action obeys the ordinary group multiplication law, even
though the virtual matrices obey only a projective one. -/
theorem ProjectiveRepresentation.adjoint_mul
    (ρ : ProjectiveRepresentation (D := D) ω) (g h : G)
    (M : Matrix (Fin D) (Fin D) ℂ) :
    ρ.adjoint (g * h) M = ρ.adjoint g (ρ.adjoint h M) := by
  have hmul : ρ.X g * ρ.X h =
      Matrix.GeneralLinearGroup.scalar (Fin D) (ω g h) * ρ.X (g * h) := by
    apply Units.ext
    simpa only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul] using ρ.map_mul g h
  calc
    ρ.adjoint (g * h) M
        = (ρ.X (g * h)).val * M * ((ρ.X (g * h))⁻¹).val := rfl
    _ = (Matrix.GeneralLinearGroup.scalar (Fin D) (ω g h) * ρ.X (g * h)).val *
          M * ((Matrix.GeneralLinearGroup.scalar (Fin D) (ω g h) *
            ρ.X (g * h))⁻¹).val :=
          (scalar_mul_adjoint (ω g h) (ρ.X (g * h)) M).symm
    _ = (ρ.X g * ρ.X h).val * M * ((ρ.X g * ρ.X h)⁻¹).val := by rw [hmul]
    _ = ρ.adjoint g (ρ.adjoint h M) := by
      simp only [ProjectiveRepresentation.adjoint, mul_inv_rev, Units.val_mul]
      simp only [Matrix.mul_assoc]

/-- The identity of the symmetry group acts trivially on bond matrices. -/
theorem ProjectiveRepresentation.adjoint_one
    (ρ : ProjectiveRepresentation (D := D) ω)
    (M : Matrix (Fin D) (Fin D) ℂ) : ρ.adjoint 1 M = M := by
  have hmul : ρ.X 1 * ρ.X 1 =
      Matrix.GeneralLinearGroup.scalar (Fin D) (ω 1 1) * ρ.X 1 := by
    apply Units.ext
    simpa only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, one_mul] using ρ.map_mul 1 1
  have hscalar : ρ.X 1 = Matrix.GeneralLinearGroup.scalar (Fin D) (ω 1 1) := by
    simpa only [one_mul] using mul_right_cancel hmul
  rw [ProjectiveRepresentation.adjoint, hscalar]
  simpa using scalar_mul_adjoint (ω 1 1) (1 : GL (Fin D) ℂ) M

/-- Conjugation by a virtual projective matrix is a complex-linear map on
the bond matrix algebra. -/
def ProjectiveRepresentation.adjointLinear
    (ρ : ProjectiveRepresentation (D := D) ω) (g : G) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ where
  toFun := ρ.adjoint g
  map_add' A B := by simp [ProjectiveRepresentation.adjoint, Matrix.mul_add,
    Matrix.add_mul]
  map_smul' c A := by simp [ProjectiveRepresentation.adjoint]

/-- The adjoint action of a projective representation is an ordinary linear
representation on bond matrices. This is the linear physical action on the
matrix-unit fixed point before a physical basis is chosen. -/
def ProjectiveRepresentation.adjointRepresentation
    (ρ : ProjectiveRepresentation (D := D) ω) :
    G →* Module.End ℂ (Matrix (Fin D) (Fin D) ℂ) where
  toFun := ρ.adjointLinear
  map_one' := by
    apply LinearMap.ext
    intro M
    change ρ.adjoint 1 M = M
    exact ρ.adjoint_one M
  map_mul' g h := by
    apply LinearMap.ext
    intro M
    change ρ.adjoint (g * h) M = ρ.adjoint g (ρ.adjoint h M)
    exact ρ.adjoint_mul g h M

/-- Matrix units, indexed by the product physical alphabet through
`finProdFinEquiv`. -/
noncomputable def matrixUnitBasis (D : ℕ) :
    Basis (Fin (D * D)) ℂ (Matrix (Fin D) (Fin D) ℂ) :=
  (Matrix.stdBasis ℂ (Fin D) (Fin D)).reindex finProdFinEquiv

/-- The ordinary matrix representation obtained by expressing the
projective adjoint action in the matrix-unit basis. It acts on a space of
dimension `D²`. -/
noncomputable def ProjectiveRepresentation.adjointMatrix
    (ρ : ProjectiveRepresentation (D := D) ω) :
    G →* Matrix (Fin (D * D)) (Fin (D * D)) ℂ where
  toFun g := LinearMap.toMatrix (matrixUnitBasis D) (matrixUnitBasis D)
    (ρ.adjointLinear g)
  map_one' := by
    rw [← LinearMap.toMatrix_one (matrixUnitBasis D)]
    congr 1
    exact ρ.adjointRepresentation.map_one
  map_mul' g h := by
    rw [← LinearMap.toMatrix_mul]
    congr 1
    exact ρ.adjointRepresentation.map_mul g h

/-- The on-site matrix for the matrix-unit MPS. Its transpose and inverse
conventions ensure that its row indexed by `i` expands the virtual
conjugation of the letter `E_i`. -/
noncomputable def ProjectiveRepresentation.onSiteMatrix
    (ρ : ProjectiveRepresentation (D := D) ω) :
    G →* Matrix (Fin (D * D)) (Fin (D * D)) ℂ where
  toFun g := (ρ.adjointMatrix g⁻¹)ᵀ
  map_one' := by simp
  map_mul' g h := by
    change (ρ.adjointMatrix (g * h)⁻¹)ᵀ =
      (ρ.adjointMatrix g⁻¹)ᵀ * (ρ.adjointMatrix h⁻¹)ᵀ
    rw [mul_inv_rev, (ρ.adjointMatrix).map_mul, Matrix.transpose_mul]

/-- Each row of the on-site matrix expands the virtual conjugation of the
corresponding matrix unit. This is the local symmetry identity in the basis
of the matrix-unit fixed point. -/
theorem ProjectiveRepresentation.onSiteMatrix_sum_basis
    (ρ : ProjectiveRepresentation (D := D) ω) (g : G)
    (i : Fin (D * D)) :
    (∑ j : Fin (D * D), ρ.onSiteMatrix g i j • matrixUnitBasis D j) =
      ρ.adjoint g⁻¹ (matrixUnitBasis D i) := by
  convert (matrixUnitBasis D).sum_repr
    (ρ.adjoint g⁻¹ (matrixUnitBasis D i)) using 1
  congr 1
  funext j
  change (ρ.adjointMatrix g⁻¹)ᵀ i j • matrixUnitBasis D j = _
  rw [Matrix.transpose_apply]
  change (LinearMap.toMatrix (matrixUnitBasis D) (matrixUnitBasis D)
    (ρ.adjointLinear g⁻¹)) j i • matrixUnitBasis D j = _
  rw [LinearMap.toMatrix_apply]
  rfl

/-- Matrix entries of the physical action in the product basis. The first
factor is the transpose of the virtual matrix, and the second is its
inverse; this is the row convention used by `twistedTensor`. -/
theorem ProjectiveRepresentation.onSiteMatrix_apply_pairs
    (ρ : ProjectiveRepresentation (D := D) ω) (g : G)
    (a b c d : Fin D) :
    ρ.onSiteMatrix g (finProdFinEquiv (a, b)) (finProdFinEquiv (c, d)) =
      (ρ.X g⁻¹ : Matrix (Fin D) (Fin D) ℂ) c a *
        (((ρ.X g⁻¹)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) b d := by
  change (ρ.adjointMatrix g⁻¹)ᵀ
    (finProdFinEquiv (a, b)) (finProdFinEquiv (c, d)) = _
  rw [Matrix.transpose_apply]
  change (LinearMap.toMatrix (matrixUnitBasis D) (matrixUnitBasis D)
    (ρ.adjointLinear g⁻¹)) (finProdFinEquiv (c, d))
      (finProdFinEquiv (a, b)) = _
  rw [LinearMap.toMatrix_apply]
  simp only [matrixUnitBasis, Module.Basis.reindex_apply,
    Equiv.symm_apply_apply, Matrix.stdBasis_eq_single]
  rw [Module.Basis.repr_reindex_apply]
  simp only [Equiv.symm_apply_apply]
  change ((ρ.X g⁻¹ : Matrix (Fin D) (Fin D) ℂ) *
    Matrix.single a b (1 : ℂ) *
    (((ρ.X g⁻¹)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) c d = _
  rw [Matrix.mul_apply, Fintype.sum_eq_single b]
  · rw [Matrix.mul_apply, Fintype.sum_eq_single a]
    · simp
    · intro j hj
      simp [hj.symm]
  · intro x hx
    simp [Matrix.mul_apply, hx.symm]

/-- In product coordinates the physical action is the tensor product of the
transpose of the virtual matrix with its inverse. -/
theorem ProjectiveRepresentation.onSiteMatrix_eq_reindex_kronecker
    (ρ : ProjectiveRepresentation (D := D) ω) (g : G) :
    ρ.onSiteMatrix g = Matrix.reindex finProdFinEquiv finProdFinEquiv
      ((ρ.X g⁻¹ : Matrix (Fin D) (Fin D) ℂ)ᵀ ⊗ₖ
        (((ρ.X g⁻¹)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
  ext p q
  obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨c, d⟩, rfl⟩ := finProdFinEquiv.surjective q
  simp only [ProjectiveRepresentation.onSiteMatrix_apply_pairs,
    Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.kroneckerMap_apply, Matrix.transpose_apply]

/-- If every virtual matrix is unitary, then the induced on-site physical
representation is unitary. In the row convention, it is the reindexed tensor
product `X(g⁻¹)ᵀ ⊗ X(g⁻¹)⁻¹`. -/
theorem ProjectiveRepresentation.onSiteMatrix_mem_unitaryGroup
    (ρ : ProjectiveRepresentation (D := D) ω)
    (hρ : ∀ g : G, (ρ.X g : Matrix (Fin D) (Fin D) ℂ) ∈
      Matrix.unitaryGroup (Fin D) ℂ) (g : G) :
    ρ.onSiteMatrix g ∈ Matrix.unitaryGroup (Fin (D * D)) ℂ := by
  rw [ρ.onSiteMatrix_eq_reindex_kronecker g]
  apply Matrix.reindex_mem_unitaryGroup
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

end TNLean.Algebra

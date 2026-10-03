/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.RepresentationTheory.Basic
import TNLean.Algebra.PermutationMatrixUnitary

/-!
# Representations in orthonormal coordinates

Given a basis, its coordinate space carries the inner product for which the basis is
orthonormal. Unitarity in these coordinates is preserved by tensor products and by the
contragredient representation in the dual basis. The left regular representation is
unitary in its group basis.

These elementary facts supply the orthonormal product bases used in Schuch, Cirac,
and Pérez-García, arXiv:1001.3807, Section 6, particularly Lemma 6.2.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open Module LinearMap Representation TensorProduct
open scoped Matrix Kronecker

namespace TNLean.PEPS

section Coordinates

variable {X Y : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Express a linear map in the specified input and output bases. -/
noncomputable def basisCoordinates (bX : Basis ι ℂ X) (bY : Basis κ ℂ Y)
    (T : X →ₗ[ℂ] Y) : (ι → ℂ) →ₗ[ℂ] (κ → ℂ) :=
  bY.equivFun.toLinearMap ∘ₗ T ∘ₗ bX.equivFun.symm.toLinearMap

/-- Express a representation in the specified basis. -/
noncomputable def basisRepresentation {G : Type*} [Group G] (bX : Basis ι ℂ X)
    (ρ : Representation ℂ G X) : Representation ℂ G (ι → ℂ) :=
  (bX.equivFun.conjAlgEquiv ℂ).toMonoidHom.comp ρ

omit [DecidableEq κ] in
@[simp]
theorem toMatrix_basisCoordinates (bX : Basis ι ℂ X) (bY : Basis κ ℂ Y)
    (T : X →ₗ[ℂ] Y) :
    LinearMap.toMatrix' (basisCoordinates bX bY T) = LinearMap.toMatrix bX bY T := rfl

omit [DecidableEq ι] in
@[simp]
theorem basisRepresentation_apply {G : Type*} [Group G] (bX : Basis ι ℂ X)
    (ρ : Representation ℂ G X) (g : G) (x : ι → ℂ) :
    basisRepresentation bX ρ g x = bX.equivFun (ρ g (bX.equivFun.symm x)) := rfl

variable {Z : Type*} [AddCommGroup Z] [Module ℂ Z]
variable {υ : Type*} [Fintype υ] [DecidableEq υ]

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq υ] in
@[simp]
theorem basisCoordinates_comp (bX : Basis ι ℂ X) (bY : Basis κ ℂ Y)
    (bZ : Basis υ ℂ Z) (S : Y →ₗ[ℂ] Z) (T : X →ₗ[ℂ] Y) :
    basisCoordinates bX bZ (S ∘ₗ T) =
      basisCoordinates bY bZ S ∘ₗ basisCoordinates bX bY T := by
  classical
  ext x
  simp [basisCoordinates]

end Coordinates

section UnitaryMatrices

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A complex matrix preserves the coordinate inner product exactly when it is unitary. -/
theorem matrix_mem_unitaryGroup_iff_dotProduct (M : Matrix ι ι ℂ) :
    M ∈ Matrix.unitaryGroup ι ℂ ↔
      ∀ x y : ι → ℂ, star (M *ᵥ x) ⬝ᵥ (M *ᵥ y) = star x ⬝ᵥ y := by
  rw [Matrix.mem_unitaryGroup_iff']
  constructor
  · intro h x y
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      ← Matrix.star_eq_conjTranspose, h, Matrix.vecMul_one]
  · intro h
    ext i j
    simpa [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      dotProduct, Matrix.mulVec_single_one, Matrix.col, Pi.single_apply, Matrix.one_apply, eq_comm]
      using h (Pi.single i 1) (Pi.single j 1)

end UnitaryMatrices

section UnitaryRepresentations

variable {G X Y : Type*} [Group G]
  [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The matrix of a representation in coordinates is its matrix in the chosen basis. -/
@[simp]
theorem toMatrix_basisRepresentation (bX : Basis ι ℂ X) (ρ : Representation ℂ G X) (g : G) :
    LinearMap.toMatrix' (basisRepresentation bX ρ g) = LinearMap.toMatrix bX bX (ρ g) := rfl

/-- Unitarity in orthonormal coordinates is equivalent to unitarity of the basis matrices. -/
theorem basisRepresentation_unitary_iff (bX : Basis ι ℂ X) (ρ : Representation ℂ G X) :
    (∀ g x y, star (basisRepresentation bX ρ g x) ⬝ᵥ basisRepresentation bX ρ g y =
      star x ⬝ᵥ y) ↔ ∀ g, LinearMap.toMatrix bX bX (ρ g) ∈ Matrix.unitaryGroup ι ℂ := by
  simp_rw [← toMatrix_basisRepresentation, matrix_mem_unitaryGroup_iff_dotProduct,
    LinearMap.toMatrix'_mulVec]

omit [DecidableEq ι] [DecidableEq κ] in
/-- Tensor products of representations unitary in the chosen bases are unitary in
the product basis. -/
theorem basisRepresentation_unitary_tensorProduct (bX : Basis ι ℂ X) (bY : Basis κ ℂ Y)
    (ρ : Representation ℂ G X) (σ : Representation ℂ G Y)
    (hρ : ∀ g x y, star (basisRepresentation bX ρ g x) ⬝ᵥ basisRepresentation bX ρ g y =
      star x ⬝ᵥ y)
    (hσ : ∀ g x y, star (basisRepresentation bY σ g x) ⬝ᵥ basisRepresentation bY σ g y =
      star x ⬝ᵥ y) :
    ∀ g x y, star (basisRepresentation (bX.tensorProduct bY) (ρ.tprod σ) g x) ⬝ᵥ
      basisRepresentation (bX.tensorProduct bY) (ρ.tprod σ) g y = star x ⬝ᵥ y := by
  classical
  apply (basisRepresentation_unitary_iff _ _).mpr
  intro g
  rw [Representation.tprod_apply, TensorProduct.toMatrix_map]
  exact Matrix.kronecker_mem_unitary ((basisRepresentation_unitary_iff bX ρ).mp hρ g)
    ((basisRepresentation_unitary_iff bY σ).mp hσ g)

/-- The contragredient of a representation unitary in a chosen basis is unitary in the
corresponding dual basis. -/
theorem basisRepresentation_unitary_dual (bX : Basis ι ℂ X) (ρ : Representation ℂ G X)
    (hρ : ∀ g x y, star (basisRepresentation bX ρ g x) ⬝ᵥ basisRepresentation bX ρ g y =
      star x ⬝ᵥ y) :
    ∀ g x y, star (basisRepresentation bX.dualBasis ρ.dual g x) ⬝ᵥ
      basisRepresentation bX.dualBasis ρ.dual g y = star x ⬝ᵥ y := by
  apply (basisRepresentation_unitary_iff _ _).mpr
  intro g
  rw [Representation.dual_apply, LinearMap.toMatrix_transpose,
    Matrix.transpose_mem_unitaryGroup_iff]
  exact (basisRepresentation_unitary_iff bX ρ).mp hρ g⁻¹

end UnitaryRepresentations

section RegularRepresentation

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The left regular representation sends the group basis vector at \(a\) to that at \(ga\),
and hence has a permutation matrix. -/
theorem toMatrix_leftRegular (g : G) :
    LinearMap.toMatrix (MonoidAlgebra.basis G ℂ) (MonoidAlgebra.basis G ℂ)
        (Representation.leftRegular ℂ G g) =
      Matrix.permMatrixHom (R := ℂ) (MulAction.toPermHom G G g) := by
  ext i j
  simp only [leftRegular, toMatrix_apply, MonoidAlgebra.basis_apply, ofMulAction_single,
    smul_eq_mul, MulAction.toPermHom_apply, Matrix.permMatrixHom_apply,
    Equiv.Perm.permMatrix, Equiv.Perm.inv_def, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    MulAction.toPerm_symm_apply, Option.mem_def, Option.some.injEq]
  change (MonoidAlgebra.single (g * j) (1 : ℂ)).coeff i =
    if g⁻¹ * i = j then 1 else 0
  simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply, inv_mul_eq_iff_eq_mul]
  simp only [eq_comm]

omit [DecidableEq G] in
/-- The left regular representation is unitary in its group basis. -/
theorem basisRepresentation_unitary_leftRegular :
    ∀ g x y, star (basisRepresentation (MonoidAlgebra.basis G ℂ)
        (Representation.leftRegular ℂ G) g x) ⬝ᵥ
      basisRepresentation (MonoidAlgebra.basis G ℂ)
        (Representation.leftRegular ℂ G) g y = star x ⬝ᵥ y := by
  classical
  apply (basisRepresentation_unitary_iff _ _).mpr
  intro g
  rw [toMatrix_leftRegular, Matrix.permMatrixHom_apply]
  exact ((MulAction.toPermHom G G g)⁻¹).permMatrix_mem_unitaryGroup

end RegularRepresentation

end TNLean.PEPS

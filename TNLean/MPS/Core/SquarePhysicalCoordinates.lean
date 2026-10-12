/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.PhysicalRotation
import TNLean.MPS.Chain.OneSidedInverse
import TNLean.Algebra.MatrixSingleSpan
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Invertible physical coordinates on an injective square support

An injective tensor with exactly `D²` physical letters differs from the raw
matrix-unit tensor by an invertible physical matrix. This supplies bounded
physical changes at the finitely many boundary sites of the extended
endpoint chains in arXiv:2203.12563, Section 5, lines 1690–1692.
No uniform many-body gap follows from this algebraic coordinate change alone.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- The raw matrix-unit tensor, without a normalization factor.
Source context: arXiv:2203.12563, Section 5, `defAgamma`, mixed-sector letters. -/
def matrixUnitPhysicalTensor (D : ℕ) : MPSTensor (D * D) D :=
  fun p => Matrix.single (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2 1

/-- The physical coefficient matrix relative to raw matrix units.
Source context: arXiv:2203.12563, Section 5, lines 1580–1601 and 1690–1692. -/
def squarePhysicalCoordinates {D : ℕ} (A : MPSTensor (D * D) D) :
    Matrix (Fin (D * D)) (Fin (D * D)) ℂ :=
  fun i p => A i (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2

/-- Raw matrix units span the full bond algebra in every dimension.
Source context: arXiv:2203.12563, Section 5, `defAgamma`. -/
theorem isInjective_matrixUnitPhysicalTensor (D : ℕ) :
    Kraus.IsInjective (matrixUnitPhysicalTensor D) := by
  apply Submodule.eq_top_of_forall_single_mem
  intro a b
  exact Submodule.subset_span ⟨finProdFinEquiv (a, b), by simp [matrixUnitPhysicalTensor]⟩

/-- The physical coefficient matrix reconstructs the tensor from raw units.
Source context: arXiv:2203.12563, Section 5, lines 1580–1601. -/
theorem rotatePhysical_squarePhysicalCoordinates {D : ℕ}
    (A : MPSTensor (D * D) D) :
    rotatePhysical (squarePhysicalCoordinates A) (matrixUnitPhysicalTensor D) = A := by
  ext i a b
  simp only [rotatePhysical, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [← (finProdFinEquiv : Fin D × Fin D ≃ Fin (D * D)).sum_comp
    (fun p => squarePhysicalCoordinates A i p * matrixUnitPhysicalTensor D p a b)]
  simp [squarePhysicalCoordinates, matrixUnitPhysicalTensor, Fintype.sum_prod_type,
    Matrix.single_apply, ite_and]

/-- On a square physical support, tensor injectivity makes the physical
coefficient matrix invertible. No polar decomposition is required.
Source context: arXiv:2203.12563, Section 5, lines 1580–1601. -/
theorem isUnit_squarePhysicalCoordinates {D : ℕ}
    (A : MPSTensor (D * D) D) (hA : Kraus.IsInjective A) :
    IsUnit (squarePhysicalCoordinates A) := by
  apply Matrix.vecMul_surjective_iff_isUnit.mp
  intro x
  let X : Matrix (Fin D) (Fin D) ℂ := fun a b => x (finProdFinEquiv (a, b))
  obtain ⟨c, hc⟩ := hA.exists_decomposition X
  refine ⟨c, ?_⟩
  funext p
  have h := congrArg (fun M => M (finProdFinEquiv.symm p).1
    (finProdFinEquiv.symm p).2) hc.symm
  simpa only [X, squarePhysicalCoordinates, Matrix.vecMul_apply_eq_sum,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Prod.mk.eta,
    Equiv.apply_symm_apply] using h

/-- The inverse physical coefficient matrix sends the actual injective
tensor to raw matrix units. Applying it at a boundary therefore replaces
that boundary tensor by a fixed isometric coordinate tensor.
Source context: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem rotatePhysical_inv_squarePhysicalCoordinates {D : ℕ}
    (A : MPSTensor (D * D) D) (hA : Kraus.IsInjective A) :
    rotatePhysical (squarePhysicalCoordinates A)⁻¹ A = matrixUnitPhysicalTensor D := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_squarePhysicalCoordinates A hA)
  calc
    rotatePhysical (squarePhysicalCoordinates A)⁻¹ A =
        rotatePhysical (squarePhysicalCoordinates A)⁻¹
          (rotatePhysical (squarePhysicalCoordinates A) (matrixUnitPhysicalTensor D)) :=
      congrArg (rotatePhysical (squarePhysicalCoordinates A)⁻¹)
        (rotatePhysical_squarePhysicalCoordinates A).symm
    _ = matrixUnitPhysicalTensor D := by
      rw [rotatePhysical_rotatePhysical, Matrix.nonsing_inv_mul _ hdet, rotatePhysical_one]

end MPSTensor

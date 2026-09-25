/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Algebra.ComplexOfRing
import TNLean.MPS.MPDO.ActionTensor
import TNLean.MPS.MPDO.OperatorProduct

/-!
# Bond-space products and actions over a ring embedded in the complex numbers

The worked examples of compression data are given by matrices over a commutative ring with
decidable equality, and their bond-space products and actions are decided in that ring before
being transported to the complex matrices by an entrywise ring homomorphism. This file records
the bond-space product and the bond-space action over an arbitrary commutative ring, in the bond
order of `finProdFinEquiv` that `MPOTensor.mulTensor` and `MPOTensor.actTensor` use, together
with their compatibility with the entrywise image of `MPSTensor.complexOfRing`.

## Main definitions

* `MPSTensor.mulTensorR`: the bond-space product of two matrix product operator tensors over a
  commutative ring.
* `MPSTensor.actTensorR`: the bond-space action of a matrix product operator tensor over a
  commutative ring on a matrix product state tensor over the same ring.

## Main results

* `MPSTensor.mulTensor_complexOfRing`, `MPSTensor.actTensor_complexOfRing`: the bond-space
  product and action commute with the entrywise image.
* `MPSTensor.mulTensor_smul_complexOfRing`: the bond-space product of two entrywise images each
  rescaled by one complex scalar is the square of that scalar times the entrywise image of the
  bond-space product.
-/

open scoped Matrix Kronecker

namespace MPSTensor

variable {R : Type*} [CommRing R] (f : R →+* ℂ) {d D₁ D₂ : ℕ}

/-- The bond-space product of two tensors over a commutative ring,
`(M · N)^{ik} = ∑_j M^{ij} ⊗ N^{jk}`, in the bond order of `finProdFinEquiv`, matching
`MPOTensor.mulTensor`. -/
def mulTensorR (M : Fin d → Fin d → Matrix (Fin D₁) (Fin D₁) R)
    (N : Fin d → Fin d → Matrix (Fin D₂) (Fin D₂) R) (i k : Fin d) :
    Matrix (Fin (D₁ * D₂)) (Fin (D₁ * D₂)) R :=
  (∑ j : Fin d, (M i j) ⊗ₖ (N j k)).submatrix finProdFinEquiv.symm finProdFinEquiv.symm

/-- The bond-space action of a matrix product operator tensor over a commutative ring on a
matrix product state tensor over the same ring, `(M · A)^i = ∑_j M^{ij} ⊗ A^j`, in the bond
order of `finProdFinEquiv`, matching `MPOTensor.actTensor`. -/
def actTensorR (M : Fin d → Fin d → Matrix (Fin D₁) (Fin D₁) R)
    (A : Fin d → Matrix (Fin D₂) (Fin D₂) R) (i : Fin d) :
    Matrix (Fin (D₁ * D₂)) (Fin (D₁ * D₂)) R :=
  (∑ j : Fin d, (M i j) ⊗ₖ (A j)).submatrix finProdFinEquiv.symm finProdFinEquiv.symm

/-- The bond-space product of two tensors rescaled by one complex scalar is the entrywise image
of their bond-space product, rescaled by the square of that scalar. -/
theorem mulTensor_smul_complexOfRing (c : ℂ)
    (M : Fin d → Fin d → Matrix (Fin D₁) (Fin D₁) R)
    (N : Fin d → Fin d → Matrix (Fin D₂) (Fin D₂) R) (i k : Fin d) :
    MPOTensor.mulTensor (fun i j => c • complexOfRing f (M i j))
        (fun i j => c • complexOfRing f (N i j)) i k =
      (c * c) • complexOfRing f (mulTensorR M N i k) := by
  ext x y
  simp only [MPOTensor.mulTensor_apply, mulTensorR, Matrix.submatrix_apply, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.kroneckerMap_apply, complexOfRing_apply, smul_eq_mul, map_sum,
    map_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The bond-space product commutes with the entrywise image. -/
theorem mulTensor_complexOfRing (M : Fin d → Fin d → Matrix (Fin D₁) (Fin D₁) R)
    (N : Fin d → Fin d → Matrix (Fin D₂) (Fin D₂) R) (i k : Fin d) :
    MPOTensor.mulTensor (fun i j => complexOfRing f (M i j))
        (fun i j => complexOfRing f (N i j)) i k =
      complexOfRing f (mulTensorR M N i k) := by
  simpa using mulTensor_smul_complexOfRing f 1 M N i k

/-- The bond-space action commutes with the entrywise image. -/
theorem actTensor_complexOfRing (M : Fin d → Fin d → Matrix (Fin D₁) (Fin D₁) R)
    (A : Fin d → Matrix (Fin D₂) (Fin D₂) R) (i : Fin d) :
    MPOTensor.actTensor (fun i j => complexOfRing f (M i j))
        (fun j => complexOfRing f (A j)) i =
      complexOfRing f (actTensorR M A i) := by
  ext x y
  simp only [MPOTensor.actTensor_apply, actTensorR, Matrix.submatrix_apply, Matrix.sum_apply,
    Matrix.kroneckerMap_apply, complexOfRing_apply, map_sum, map_mul]

end MPSTensor

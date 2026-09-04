/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.OperatorProduct
import TNLean.MPS.MPDO.PhysicalAdjoint

/-!
# Physical adjunction reverses the operator product of MPO tensors

Physical adjunction conjugates every coefficient of a matrix product operator
tensor and exchanges its two physical indices, leaving the virtual chain in
place.  Applied to a product tensor it exchanges the two factors, so the
adjoint of a product is the product of the adjoints in the opposite order, read
on the bond space whose two Kronecker factors have been exchanged.

The two bond spaces of the factors need not have the same dimension, so the
exchange of the two factors of a product bond space is recorded here for
unequal dimensions.

## Main definitions

* `MPOTensor.bondProdSwapEquiv` — exchange of the two factors of a product bond
  space of unequal dimensions.

## Main results

* `MPOTensor.physicalAdjointTensor_mulTensor` — the physical adjoint of a
  product tensor is the reversed product of the physical adjoints, reindexed by
  the product-bond exchange.

## References

* Cirac--Garre-Rubio--Pérez-García--Ruiz-de-Alarcón--Schuch, arXiv:2502.20257,
  line 1662, for the description of the dagger operation used here, and the
  proof of Proposition `prop:zetas`, lines 1662--1677, for the inverse-product
  step it serves.
-/

open scoped Matrix BigOperators Kronecker

namespace MPOTensor

variable {d D₁ D₂ : ℕ}

/-- Exchange of the two factors of a product bond space: the flattened index of
a pair `(a, b)` is sent to the flattened index of `(b, a)`.

Unlike `bondPairSwapEquiv`, the two factors are allowed to have different
dimensions.

Source: arXiv:2502.20257, line 1662, where the dagger operation swaps the two
legs lying on the same side of a tensor. -/
def bondProdSwapEquiv (D₁ D₂ : ℕ) : Fin (D₁ * D₂) ≃ Fin (D₂ * D₁) :=
  finProdFinEquiv.symm.trans
    ((Equiv.prodComm (Fin D₁) (Fin D₂)).trans finProdFinEquiv)

@[simp] theorem bondProdSwapEquiv_finProdFinEquiv (a : Fin D₁) (b : Fin D₂) :
    bondProdSwapEquiv D₁ D₂ (finProdFinEquiv (a, b)) = finProdFinEquiv (b, a) := by
  simp [bondProdSwapEquiv]

@[simp] theorem bondProdSwapEquiv_symm :
    (bondProdSwapEquiv D₁ D₂).symm = bondProdSwapEquiv D₂ D₁ := by
  refine Equiv.ext fun x => ?_
  obtain ⟨⟨b, a⟩, rfl⟩ := finProdFinEquiv.surjective x
  rw [Equiv.symm_apply_eq, bondProdSwapEquiv_finProdFinEquiv,
    bondProdSwapEquiv_finProdFinEquiv]

/-- **Physical adjunction reverses the operator product.** The physical adjoint
of a product tensor is the product of the physical adjoints of its factors in
the opposite order, read on the product bond space with its two factors
exchanged.

Source: arXiv:2502.20257, the dagger operation described at line 1662 and the
inverse-product step in the proof of Proposition `prop:zetas`, lines
1662--1677. -/
theorem physicalAdjointTensor_mulTensor (M : MPOTensor d D₁) (N : MPOTensor d D₂)
    (i k : Fin d) :
    physicalAdjointTensor (mulTensor M N) i k =
      (mulTensor (physicalAdjointTensor N) (physicalAdjointTensor M) i k).submatrix
        (bondProdSwapEquiv D₁ D₂) (bondProdSwapEquiv D₁ D₂) := by
  ext x y
  obtain ⟨⟨x₁, x₂⟩, rfl⟩ := finProdFinEquiv.surjective x
  obtain ⟨⟨y₁, y₂⟩, rfl⟩ := finProdFinEquiv.surjective y
  simp only [physicalAdjointTensor_apply, mulTensor_apply, Matrix.submatrix_apply,
    Matrix.sum_apply, Matrix.kronecker_apply, Equiv.symm_apply_apply,
    bondProdSwapEquiv_finProdFinEquiv, star_sum, star_mul']
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end MPOTensor

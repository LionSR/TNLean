/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.OperatorProduct
import TNLean.MPS.MPU.TransferMatrix

/-!
# Normalized flattening of a composition tensor

This file relates the normalized flattening of the composition tensor to the
normalized flattenings of its two factors.

## Main results

* `MPOTensor.normalizedFlattening_mulTensor_apply`: the physical contraction
  formula, with the doubled auxiliary indices in their canonical order.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188], equation
  `eq:transfer-op`, lines 336--340, and the proof of Theorem `IndexTh`, lines
  837--841.
-/

open scoped Matrix BigOperators Kronecker

namespace MPOTensor

variable {d D₁ D₂ : ℕ}

/-- The normalized flattening of the composition tensor is the physical
contraction of the two normalized flattenings, multiplied by the scalar
$\sqrt d$.
The auxiliary pairs are encoded by `finProdFinEquiv` in the same order as in
`MPOTensor.mulTensor`.

This combines the raw composition tensor in arXiv:1703.09188, proof of Theorem
`IndexTh`, lines 837--841, with the normalization in equation
`eq:transfer-op`, lines 336--340; it is not a separately stated result of the
paper. -/
lemma normalizedFlattening_mulTensor_apply [NeZero d]
    (U : MPOTensor d D₁) (V : MPOTensor d D₂) (i k : Fin d) :
    (mulTensor U V).normalizedFlattening (finProdFinEquiv (i, k)) =
      (Real.sqrt d : ℂ) •
        (∑ j : Fin d,
          U.normalizedFlattening (finProdFinEquiv (i, j)) ⊗ₖ
            V.normalizedFlattening (finProdFinEquiv (j, k))).submatrix
              finProdFinEquiv.symm finProdFinEquiv.symm := by
  classical
  have hd : (0 : ℝ) < d := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hsqrt : (Real.sqrt d : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr hd
  ext a b
  simp only [normalizedFlattening, mulTensor_apply, toMPSTensor,
    MPSTensor.finProdFinEquiv_divNat, MPSTensor.finProdFinEquiv_modNat,
    Matrix.smul_apply, Matrix.submatrix_apply, Matrix.sum_apply,
    Matrix.kroneckerMap_apply, smul_eq_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  field_simp

end MPOTensor

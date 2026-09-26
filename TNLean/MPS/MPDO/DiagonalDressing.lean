/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ListProduct
import TNLean.MPS.Core.LetterScaledNormality
import TNLean.MPS.MPDO.Defs

/-!
# Dressing a matrix product operator by a diagonal on-site operator

Let `M` be a matrix product operator tensor with periodic operators `O_N`, and let
`c : Fin d → ℂ` be the diagonal of an on-site operator `Δ = diag(c)`. Multiplying the letter
`M^{ij}` by `c j` gives the tensor whose periodic operators are `O_N Δ^{⊗N}`: the on-site
operator acts first, on the input leg. On the doubled-index tensor the dressing rescales every
letter by a scalar, so it preserves normality when `c` has no zero entries.

## Main definitions

* `MPOTensor.mulDiagonal`: the dressed tensor `(M.mulDiagonal c)^{ij} = c j • M^{ij}`.

## Main results

* `MPOTensor.mpo_mulDiagonal`: `mpo (M.mulDiagonal c) N = mpo M N * diag(∏_k c (t k))`.
* `MPOTensor.isNormal_toMPSTensor_mulDiagonal_iff`: for `c` without zero entries, the dressed
  doubled-index tensor is normal exactly when the original one is.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608, Section 4.1, lines 623--630
  (the periodic operator `O_N` of a matrix product operator tensor).
-/

open scoped Matrix

namespace MPOTensor

variable {d D : ℕ}

/-- **Dressing by a diagonal on-site operator.** The letter `(i, j)` of `M` multiplied by the
diagonal entry `c j` at the input index; the periodic operators are those of `M` followed by
the on-site operator `diag(c)` applied first (`MPOTensor.mpo_mulDiagonal`). -/
def mulDiagonal (M : MPOTensor d D) (c : Fin d → ℂ) : MPOTensor d D :=
  fun i j ↦ c j • M i j

@[simp] theorem mulDiagonal_apply (M : MPOTensor d D) (c : Fin d → ℂ) (i j : Fin d) :
    M.mulDiagonal c i j = c j • M i j := rfl

/-- **The periodic operators of a dressed tensor**: `O_N diag(c)^{⊗N}`, where `diag(c)^{⊗N}` is
the diagonal matrix with entry `∏_k c (t k)` at the configuration `t`.

Source: arXiv:1606.00608, lines 623--630 (the periodic operator), with the dressing on the input
leg. -/
theorem mpo_mulDiagonal (M : MPOTensor d D) (c : Fin d → ℂ) (N : ℕ) :
    mpo (M.mulDiagonal c) N = mpo M N * Matrix.diagonal fun t ↦ ∏ k, c (t k) := by
  ext σ τ
  simp only [mpo_apply, mpoMatrixEntry, evalWord_ofFn, mulDiagonal_apply, List.prod_ofFn_smul,
    Matrix.trace_smul, Matrix.mul_diagonal, smul_eq_mul]
  ring

/-- The doubled-index letter `(i, j)` of a dressed tensor is that of the original tensor
multiplied by `c j`. -/
theorem toMPSTensor_mulDiagonal (M : MPOTensor d D) (c : Fin d → ℂ) :
    (M.mulDiagonal c).toMPSTensor = fun a ↦ c a.modNat • M.toMPSTensor a := rfl

/-- **Dressing by an invertible diagonal on-site operator preserves normality** of the
doubled-index tensor: every letter is rescaled by a nonzero scalar. -/
theorem isNormal_toMPSTensor_mulDiagonal_iff (M : MPOTensor d D) {c : Fin d → ℂ}
    (hc : ∀ j, c j ≠ 0) :
    Kraus.IsNormal (M.mulDiagonal c).toMPSTensor ↔ Kraus.IsNormal M.toMPSTensor := by
  rw [toMPSTensor_mulDiagonal]
  exact MPSTensor.isNormal_letterSmul_iff (fun a ↦ hc a.modNat) _

end MPOTensor

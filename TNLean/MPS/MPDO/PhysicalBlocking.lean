/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.RFPViaTS

/-!
# Two-site physical blocking of MPO tensors

This file defines the tensor obtained by blocking two adjacent physical sites
of an MPO tensor and identifies its one-site and two-site physical closures
with the two-site and four-site closures of the original tensor.

## Main definitions

* `MPOTensor.blockTwo`: the tensor obtained by blocking two adjacent sites.
* `MPOTensor.physClose4`: the right-associated four-site physical closure.
* `MPOTensor.physClose1_blockTwo_eq_physClose2`: one blocked site is two original sites.
* `MPOTensor.physClose2_blockTwo_eq_physClose4`: two blocked sites are four original sites.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Theorem 4.9, lines 851--856
-/

open scoped Matrix

namespace MPOTensor

variable {d D : ℕ}

/-! ### Two-site blocking -/

/-- The MPO tensor obtained by blocking two adjacent physical sites. The two
ket indices, and separately the two bra indices, are encoded through the
standard equivalence `Fin d × Fin d ≃ Fin (d * d)`. This is the blocking used
in arXiv:1606.00608, Theorem 4.9, lines 851--856. -/
noncomputable def blockTwo (M : MPOTensor d D) : MPOTensor (d * d) D :=
  fun i j =>
    M (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1 *
      M (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2

@[simp] lemma blockTwo_apply (M : MPOTensor d D) (i j : Fin (d * d)) :
    blockTwo M i j =
      M (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1 *
        M (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2 :=
  rfl

/-! ### The four-site physical closure -/

/-- The four-site physical closure, with the physical indices associated as
`Fin d × (Fin d × (Fin d × Fin d))`. Its coefficient is the virtual trace of
four consecutive tensor matrices followed by the inserted virtual operator.
This is the four-site instance of the open physical contraction used in
arXiv:1606.00608, Definition 4.1, lines 638--657. -/
noncomputable def physClose4 (M : MPOTensor d D) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ]
      Matrix (Fin d × (Fin d × (Fin d × Fin d)))
        (Fin d × (Fin d × (Fin d × Fin d))) ℂ where
  toFun X := Matrix.of fun i j =>
    Matrix.trace
      (M i.1 j.1 * M i.2.1 j.2.1 * M i.2.2.1 j.2.2.1 *
        M i.2.2.2 j.2.2.2 * X)
  map_add' X Y := by
    ext i j
    simp [Matrix.mul_add, Matrix.trace_add]
  map_smul' c X := by
    ext i j
    simp [Matrix.trace_smul]

@[simp] lemma physClose4_apply (M : MPOTensor d D)
    (X : Matrix (Fin D) (Fin D) ℂ)
    (i j : Fin d × (Fin d × (Fin d × Fin d))) :
    physClose4 M X i j =
      Matrix.trace
        (M i.1 j.1 * M i.2.1 j.2.1 * M i.2.2.1 j.2.2.1 *
          M i.2.2.2 j.2.2.2 * X) :=
  rfl

/-- Under the canonical right-associated identification of four-site
configurations with quadruples of physical indices, the general length-four
closure is `physClose4`. -/
theorem physCloseN_four_eq_physClose4 (M : MPOTensor d D) :
    (Matrix.reindexLinearEquiv ℂ ℂ (finFourArrowEquiv (Fin d))
        (finFourArrowEquiv (Fin d))).toLinearMap ∘ₗ physCloseN M 4 =
      physClose4 M := by
  ext X i j
  simp [Matrix.coe_reindexLinearEquiv, finFourArrowEquiv, finThreeArrowEquiv,
    Matrix.mul_assoc]

/-! ### Blocking identities -/

/-- Decode one blocked physical index into its two constituent indices. -/
def blockedIndexEquiv (d : ℕ) : Fin (d * d) ≃ Fin d × Fin d :=
  finProdFinEquiv.symm

/-- Decode a pair of blocked physical indices into four right-associated
original physical indices. -/
def blockedPairEquiv (d : ℕ) :
    Fin (d * d) × Fin (d * d) ≃ Fin d × (Fin d × (Fin d × Fin d)) :=
  (Equiv.prodCongr (blockedIndexEquiv d) (blockedIndexEquiv d)).trans
    (Equiv.prodAssoc (Fin d) (Fin d) (Fin d × Fin d))

/-- After decoding the blocked physical index, the one-site closure of the
two-site blocked tensor is the two-site closure of the original tensor. -/
theorem physClose1_blockTwo_eq_physClose2 (M : MPOTensor d D) :
    (Matrix.reindexLinearEquiv ℂ ℂ (blockedIndexEquiv d)
        (blockedIndexEquiv d)).toLinearMap ∘ₗ physClose1 (blockTwo M) =
      physClose2 M := by
  ext X i j
  simp [Matrix.coe_reindexLinearEquiv, blockedIndexEquiv, blockTwo]

/-- After decoding both blocked physical indices, the two-site closure of the
two-site blocked tensor is the right-associated four-site closure of the
original tensor. -/
theorem physClose2_blockTwo_eq_physClose4 (M : MPOTensor d D) :
    (Matrix.reindexLinearEquiv ℂ ℂ (blockedPairEquiv d) (blockedPairEquiv d)).toLinearMap ∘ₗ
        physClose2 (blockTwo M) =
      physClose4 M := by
  ext X i j
  simp [Matrix.coe_reindexLinearEquiv, blockedPairEquiv, blockedIndexEquiv,
    blockTwo, Matrix.mul_assoc]

end MPOTensor

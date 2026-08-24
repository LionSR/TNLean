/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex
import QICLean.Kraus.Word
import TNLean.Algebra.FinTupleEquiv

/-!
# Independent tensor products of matrix product tensors

For matrix product tensors (A=(A^i)_i) and (B=(B^k)_k), their independent
tensor product has local matrices
\[
  (A\boxtimes B)^{(i,k)}=A^i\otimes B^k.
\]
Both the physical and virtual product indices use Mathlib's canonical
`finProdFinEquiv` coordinates.  Word evaluation separates into the two
pointwise component words.

This construction is infrastructure for the sentence "The case of tensoring
is trivial" in arXiv:1703.09188, proof of Theorem `IndexTh` (ii), lines
824--845; the paper does not state it as a separate theorem.  The matrix
product tensor notation agrees with the canonical-form block notation in
arXiv:1606.00608, equation `II_CF1`, lines 214--245.  No canonical-form or
normality assertion is made here.

## Main definitions

* `MPSTensor.tensorProduct` is the local Kronecker product in standard finite
  product coordinates.

## Main statements

* `MPSTensor.tensorProduct_apply` gives its exact matrix entries.
* `MPSTensor.evalWord_tensorProduct` separates a product-indexed word into its
  two component word evaluations.
-/

open scoped Matrix Kronecker

namespace MPSTensor

variable {d D e E : ℕ}

/-- The independent tensor product of two matrix product tensors, using
`finProdFinEquiv` on both physical and virtual indices.

This is infrastructure for the tensoring clause in arXiv:1703.09188, proof of
Theorem `IndexTh` (ii), lines 824--845, rather than a separately stated result
of that paper. -/
def tensorProduct (A : MPSTensor d D) (B : MPSTensor e E) :
    MPSTensor (d * e) (D * E) :=
  fun ik ↦ Matrix.reindex finProdFinEquiv finProdFinEquiv
    (A ik.divNat ⊗ₖ B ik.modNat)

/-- Entry formula for the independent tensor product.

This is the coordinate form of the tensoring infrastructure for
arXiv:1703.09188, proof of Theorem `IndexTh` (ii), lines 824--845, not a
separately stated theorem of the paper. -/
@[simp] theorem tensorProduct_apply (A : MPSTensor d D) (B : MPSTensor e E)
    (i : Fin d) (k : Fin e) (α β : Fin D) (γ δ : Fin E) :
    tensorProduct A B (finProdFinEquiv (i, k))
        (finProdFinEquiv (α, γ)) (finProdFinEquiv (β, δ)) =
      A i α β * B k γ δ := by
  simp only [tensorProduct, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply]
  simp only [Equiv.symm_apply_apply]
  change
    A (finProdFinEquiv.symm (finProdFinEquiv (i, k))).1 α β *
        B (finProdFinEquiv.symm (finProdFinEquiv (i, k))).2 γ δ =
      A i α β * B k γ δ
  rw [Equiv.symm_apply_apply]

/-- Evaluating a word in the independent tensor product is the reindexed
Kronecker product of the evaluations of its two pointwise component words.

This is the word form of the tensoring construction used in
arXiv:1703.09188, proof of Theorem `IndexTh` (ii), lines 824--845; it is
infrastructure, not a separately stated theorem of the paper. -/
theorem evalWord_tensorProduct (A : MPSTensor d D) (B : MPSTensor e E)
    (w : List (Fin (d * e))) :
    Kraus.evalWord (tensorProduct A B) w =
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Kraus.evalWord A (w.map Fin.divNat) ⊗ₖ
          Kraus.evalWord B (w.map Fin.modNat)) := by
  induction w with
  | nil =>
      simp [Kraus.evalWord]
  | cons i w ih =>
      simp only [Kraus.evalWord_cons, List.map_cons, tensorProduct]
      rw [ih]
      rw [← Matrix.coe_reindexRingEquiv ℂ finProdFinEquiv]
      rw [← map_mul, Matrix.mul_kronecker_mul]

end MPSTensor

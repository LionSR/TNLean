/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex
import QICLean.Kraus.Word
import TNLean.MPS.Tensor.Defs

/-!
# Independent tensor products of matrix product tensors

For matrix product tensors (A=(A^i)_i) and (B=(B^k)_k), their independent
tensor product has local matrices
\[
  (A\boxtimes B)^{(i,k)}=A^i\otimes B^k.
\]
The physical index is the pair alphabet \(\alpha\times\beta\); the virtual
product index uses Mathlib's canonical `finProdFinEquiv` coordinates.  Word
evaluation separates into the two pointwise component words.

This construction is infrastructure for the sentence "The case of tensoring
is trivial" in arXiv:1703.09188, proof of Theorem `IndexTh` (ii), lines
824--845; the paper does not state it as a separate theorem.  The matrix
product tensor notation agrees with the canonical-form block notation in
arXiv:1606.00608, equation `II_CF1`, lines 214--245.  No canonical-form or
normality assertion is made here.

## Main definitions

* `MPSTensor.tensorProduct` is the local Kronecker product on the pair
  alphabet, in standard finite product bond coordinates.

## Main statements

* `MPSTensor.tensorProduct_apply` gives its exact matrix entries.
* `MPSTensor.evalWord_tensorProduct` separates a product-indexed word into its
  two component word evaluations.
* `MPSTensor.leftCanonical_tensorProduct` proves left-canonicality directly
  from the two constituent normalization identities.
-/

open MPTensor

open scoped Matrix Kronecker

namespace MPSTensor

variable {α β : Type*} {D E : ℕ}

/-- The independent tensor product of two matrix product tensors, on the pair
physical alphabet and with `finProdFinEquiv` on the virtual indices.

This is infrastructure for the tensoring clause in arXiv:1703.09188, proof of
Theorem `IndexTh` (ii), lines 824--845, rather than a separately stated result
of that paper. -/
def tensorProduct (A : MPTensor α (Fin D)) (B : MPTensor β (Fin E)) :
    MPTensor (α × β) (Fin (D * E)) :=
  fun ik ↦ Matrix.reindex finProdFinEquiv finProdFinEquiv (A ik.1 ⊗ₖ B ik.2)

/-- Entry formula for the independent tensor product.

This is the coordinate form of the tensoring infrastructure for
arXiv:1703.09188, proof of Theorem `IndexTh` (ii), lines 824--845, not a
separately stated theorem of the paper. -/
@[simp] theorem tensorProduct_apply (A : MPTensor α (Fin D)) (B : MPTensor β (Fin E))
    (i : α) (k : β) (a b : Fin D) (c e : Fin E) :
    tensorProduct A B (i, k) (finProdFinEquiv (a, c)) (finProdFinEquiv (b, e)) =
      A i a b * B k c e := by
  simp only [tensorProduct, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, Equiv.symm_apply_apply]

/-- Evaluating a word in the independent tensor product is the reindexed
Kronecker product of the evaluations of its two pointwise component words.

This is the word form of the tensoring construction used in
arXiv:1703.09188, proof of Theorem `IndexTh` (ii), lines 824--845; it is
infrastructure, not a separately stated theorem of the paper. -/
theorem evalWord_tensorProduct (A : MPTensor α (Fin D)) (B : MPTensor β (Fin E))
    (w : List (α × β)) :
    Kraus.evalWord (tensorProduct A B) w =
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Kraus.evalWord A (w.map Prod.fst) ⊗ₖ
          Kraus.evalWord B (w.map Prod.snd)) := by
  induction w with
  | nil =>
      simp [Kraus.evalWord]
  | cons i w ih =>
      simp only [Kraus.evalWord_cons, List.map_cons, tensorProduct]
      rw [ih]
      rw [← Matrix.coe_reindexRingEquiv ℂ finProdFinEquiv]
      rw [← map_mul, Matrix.mul_kronecker_mul]

/-- Independent tensor products preserve left-canonical normalization.

If `A` and `B` satisfy
\[
  \sum_i (A^i)^\dagger A^i=\mathbf 1_D,
  \qquad
  \sum_k (B^k)^\dagger B^k=\mathbf 1_E,
\]
then the Kronecker multiplication and adjoint identities give
\[
  \sum_{i,k} ((A^i\otimes B^k)^\dagger)(A^i\otimes B^k)
  =\mathbf 1_D\otimes\mathbf 1_E=\mathbf 1_{DE}.
\]

This is project infrastructure for the tensoring clause in arXiv:1703.09188,
proof of Theorem `IndexTh` (ii), lines 824--845, not a result stated separately
in that paper.  The retained-normal-block context is
arXiv:1606.00608, equation `II_CF1`, lines 214--245; the two left-canonical
identities are explicit project hypotheses, not an assertion attributed to
that passage. -/
theorem leftCanonical_tensorProduct [Fintype α] [Fintype β]
    (A : MPTensor α (Fin D)) (B : MPTensor β (Fin E))
    (hA : IsLeftCanonical A) (hB : IsLeftCanonical B) :
    IsLeftCanonical (tensorProduct A B) := by
  classical
  unfold IsLeftCanonical Kraus.IsTP
  unfold IsLeftCanonical Kraus.IsTP at hA hB
  rw [Fintype.sum_prod_type]
  have hterm (i : α) (k : β) :
      (tensorProduct A B (i, k))ᴴ * tensorProduct A B (i, k) =
        Matrix.reindex finProdFinEquiv finProdFinEquiv
          (((A i)ᴴ * A i) ⊗ₖ ((B k)ᴴ * B k)) := by
    simp only [tensorProduct]
    rw [Matrix.conjTranspose_reindex]
    change Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv
          ((A i ⊗ₖ B k)ᴴ) *
        Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv
          (A i ⊗ₖ B k) =
      Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv
        (((A i)ᴴ * A i) ⊗ₖ ((B k)ᴴ * B k))
    rw [Matrix.reindexLinearEquiv_mul ℂ ℂ finProdFinEquiv finProdFinEquiv
      finProdFinEquiv, Matrix.conjTranspose_kronecker, Matrix.mul_kronecker_mul]
  simp_rw [hterm]
  change ∑ i : α, ∑ k : β,
      Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv
        (((A i)ᴴ * A i) ⊗ₖ ((B k)ᴴ * B k)) = 1
  apply (Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv).symm.injective
  simp only [map_sum, LinearEquiv.symm_apply_apply]
  rw [Matrix.symm_reindexLinearEquiv, Matrix.reindexLinearEquiv_one]
  have hsum :
      (∑ i : α, ∑ k : β, ((A i)ᴴ * A i) ⊗ₖ ((B k)ᴴ * B k)) =
        (∑ i : α, (A i)ᴴ * A i) ⊗ₖ (∑ k : β, (B k)ᴴ * B k) := by
    symm
    change Matrix.kroneckerBilinear (R := ℂ) (α := ℂ)
      (∑ i : α, (A i)ᴴ * A i) (∑ k : β, (B k)ᴴ * B k) = _
    rw [map_sum]
    simp_rw [map_sum]
    rw [Finset.sum_comm]
    simp only [LinearMap.sum_apply]
    rfl
  rw [hsum, hA, hB, Matrix.one_kronecker_one]

end MPSTensor

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixAux

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Vec

/-!
# The Frobenius matrix space as a Hilbert space

This file identifies a finite complex matrix space, equipped with its Frobenius
norm, with the Euclidean space of its entries.  The identification permits
finite-dimensional Hilbert-space results to be applied to matrix
superoperators without introducing a second norm on matrices.

## Main declaration

* `Matrix.frobeniusEquivEuclidean`: vectorization as a complex linear
  isometric equivalence.
* `Matrix.frobeniusEuclideanMap`: transport of a matrix superoperator through
  this equivalence.
-/

open scoped Matrix Matrix.Norms.Frobenius

namespace Matrix

/-- Column vectorization is a linear isometry from matrices with the
Frobenius norm to the Euclidean space of their entries. -/
noncomputable def frobeniusEquivEuclidean
    (m n : Type*) [Fintype m] [Fintype n] :
    Matrix m n ℂ ≃ₗᵢ[ℂ] EuclideanSpace ℂ (n × m) where
  toFun A := WithLp.toLp 2 A.vec
  invFun x := of fun i j ↦ WithLp.ofLp x (j, i)
  map_add' A B := by
    apply PiLp.ext
    intro ji
    simp
  map_smul' c A := by
    apply PiLp.ext
    intro ji
    simp
  left_inv A := by
    ext i j
    simp
  right_inv x := by
    apply PiLp.ext
    intro ji
    simp
  norm_map' A := by
    change ‖WithLp.toLp 2 A.vec‖ = ‖A‖
    rw [Matrix.frobenius_norm_def, PiLp.norm_eq_of_L2, Real.sqrt_eq_rpow]
    congr 2
    have hvec : WithLp.ofLp (WithLp.toLp 2 A.vec) = A.vec := rfl
    rw [hvec]
    simp only [Matrix.vec]
    calc
      ∑ x : n × m, ‖A x.2 x.1‖ ^ 2 =
          ∑ j : n, ∑ i : m, ‖A i j‖ ^ 2 := by
        simpa only [Finset.univ_product_univ] using
          (Finset.sum_product'
            (s := (Finset.univ : Finset n)) (t := (Finset.univ : Finset m))
            (f := fun j i ↦ ‖A i j‖ ^ 2))
      _ = ∑ i : m, ∑ j : n, ‖A i j‖ ^ 2 := Finset.sum_comm
    simp only [Real.rpow_two, pow_two]

@[simp]
theorem frobeniusEquivEuclidean_apply
    {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    frobeniusEquivEuclidean m n A = WithLp.toLp 2 A.vec :=
  rfl

@[simp]
theorem frobeniusEquivEuclidean_symm_apply
    {m n : Type*} [Fintype m] [Fintype n]
    (x : EuclideanSpace ℂ (n × m)) (i : m) (j : n) :
    (frobeniusEquivEuclidean m n).symm x i j = WithLp.ofLp x (j, i) :=
  rfl

/-- Under vectorization, the Euclidean inner product is the
Hilbert--Schmidt trace pairing. -/
theorem inner_frobeniusEquivEuclidean
    {m n : Type*} [Fintype m] [Fintype n] (A B : Matrix m n ℂ) :
    inner ℂ (frobeniusEquivEuclidean m n A)
      (frobeniusEquivEuclidean m n B) = Matrix.trace (Aᴴ * B) := by
  rw [frobeniusEquivEuclidean_apply, frobeniusEquivEuclidean_apply,
    EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  exact Matrix.star_vec_dotProduct_vec A B

/-- Transport a linear map between matrix spaces to the corresponding
Euclidean spaces of entries. -/
noncomputable def frobeniusEuclideanMap
    {α β : Type*} [Fintype α] [Fintype β]
    (E : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) :
    EuclideanSpace ℂ (α × α) →ₗ[ℂ] EuclideanSpace ℂ (β × β) :=
  (frobeniusEquivEuclidean β β).toLinearEquiv.toLinearMap.comp
    (E.comp (frobeniusEquivEuclidean α α).symm.toLinearEquiv.toLinearMap)

@[simp]
theorem frobeniusEuclideanMap_apply
    {α β : Type*} [Fintype α] [Fintype β]
    (E : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) (X : Matrix α α ℂ) :
    frobeniusEuclideanMap E (frobeniusEquivEuclidean α α X) =
      frobeniusEquivEuclidean β β (E X) := by
  change frobeniusEquivEuclidean β β
      (E ((frobeniusEquivEuclidean α α).symm
        (frobeniusEquivEuclidean α α X))) =
    frobeniusEquivEuclidean β β (E X)
  rw [(frobeniusEquivEuclidean α α).symm_apply_apply]

end Matrix

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixFamilySupport
import TNLean.Analysis.MatrixSqrt

/-!
# Joint column supports of Kronecker-product families

The joint column Gram matrix of the full product family
\(\{A_a\otimes B_b\}_{a,b}\) is the Kronecker product of the two individual
joint column Gram matrices. Consequently its joint column support is the
Kronecker product of the two individual support projections.

## Main results

* `Matrix.familyColumnGram_kronecker`: factorization of the product-family Gram.
* `Matrix.familySupportProj_kronecker`: factorization of the product-family support.
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

namespace Matrix

variable {ι κ m n p q : Type*}
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]

/-- The family consisting of all Kronecker products of one member from each
of two finite matrix families. -/
noncomputable def familyKronecker
    (A : ι → Matrix m n ℂ) (B : κ → Matrix p q ℂ) :
    ι × κ → Matrix (m × p) (n × q) ℂ :=
  fun ab ↦ A ab.1 ⊗ₖ B ab.2

omit [DecidableEq ι] [DecidableEq κ] [Fintype m] [DecidableEq m]
  [DecidableEq n] [Fintype p] [DecidableEq p] [DecidableEq q] in
/-- The joint column Gram of a full Kronecker-product family is the Kronecker
product of the two joint column Gram matrices. -/
theorem familyColumnGram_kronecker
    (A : ι → Matrix m n ℂ) (B : κ → Matrix p q ℂ) :
    familyColumnGram (familyKronecker A B) =
      familyColumnGram A ⊗ₖ familyColumnGram B := by
  rw [familyColumnGram_eq_sum, familyColumnGram_eq_sum,
    familyColumnGram_eq_sum]
  simp_rw [familyKronecker, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul]
  ext ⟨i, u⟩ ⟨j, v⟩
  simp only [Matrix.kroneckerMap_apply]
  simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq n] [DecidableEq q] in
/-- The joint column support of a full Kronecker-product family is the
Kronecker product of the two joint column supports. -/
theorem familySupportProj_kronecker
    (A : ι → Matrix m n ℂ) (B : κ → Matrix p q ℂ) :
    familySupportProj (familyKronecker A B) =
      familySupportProj A ⊗ₖ familySupportProj B := by
  let hA := familyColumnGram_posSemidef A
  let hB := familyColumnGram_posSemidef B
  let hProduct := familyColumnGram_posSemidef (familyKronecker A B)
  calc
    familySupportProj (familyKronecker A B) =
        (hA.kronecker hB).supportProj := by
      rw [familySupportProj]
      exact hProduct.supportProj_congr (hA.kronecker hB)
        (familyColumnGram_kronecker A B)
    _ = hA.supportProj ⊗ₖ hB.supportProj :=
      hA.supportProj_kronecker hB
    _ = familySupportProj A ⊗ₖ familySupportProj B := by
      rfl

end Matrix

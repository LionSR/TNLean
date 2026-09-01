/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Star.TensorProduct
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.TensorProduct.Submodule
import Mathlib.RingTheory.MatrixAlgebra
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.RingTheory.SimpleRing.Matrix
import QICLean.Algebra.SkolemNoetherUnitary

/-!
# Products of commuting star-subalgebras

Two unital star-subalgebras of a common algebra which commute elementwise define a star-algebra
homomorphism from their tensor product by multiplication. Its range is their algebraic join, and
its underlying complex vector space is the span of products of elements from the two factors.

When both factors are full matrix algebras of positive sizes, this homomorphism is injective by
simplicity. Consequently, the join is itself a full matrix algebra of the product size.

## Main definitions

* `StarSubalgebra.commutingMulMap` maps a pure tensor to the product of its two factors.
* `StarSubalgebra.commutingSupEquivMatrix` presents the join of two commuting full matrix factors.

## Main results

* `StarSubalgebra.commutingMulMap_range` identifies the range with the algebraic join.
* `StarSubalgebra.sup_toSubmodule_eq_mul` identifies the join with the linear span of products.
* `StarSubalgebra.commutingMulMap_injective_of_equiv_matrix` derives injectivity from full-matrix
  presentations of the two factors.
* `StarSubalgebra.finrank_sup_of_equiv_matrix` computes the complex dimension of the join.

## References

* B. Schumacher and R. F. Werner, *Reversible quantum cellular automata*,
  quant-ph/0405174, Proposition `Cscom`, lines 2119--2138.
* D. Gross, V. Nesme, H. Vogts, and R. F. Werner, *Index theory of one-dimensional quantum walks
  and cellular automata*, arXiv:0910.3675v2, lines 1270--1314.

**Scope restriction (full matrix, single block):** The full-matrix theorem below is only the
unital single-block specialization of `Cscom`. It does not assert the direct-sum block-pair theorem,
the multiplicity equation, or that the join fills the ambient algebra. This restriction and its
elimination plan are documented in
`docs/paper-gaps/gnvw12_cscom_single_block_scope.tex`.
-/

open scoped TensorProduct

namespace StarSubalgebra

variable {C : Type*} [Ring C] [Algebra ℂ C] [StarRing C] [StarModule ℂ C]

/-- Multiplication from the tensor product of two elementwise commuting unital star-subalgebras
into their common ambient algebra. -/
noncomputable def commutingMulMap [Nontrivial C] (A B : StarSubalgebra ℂ C)
    (hAB : ∀ a : A, ∀ b : B, Commute (a : C) (b : C)) :
    A ⊗[ℂ] B →⋆ₐ[ℂ] C where
  toAlgHom := Algebra.TensorProduct.lift A.subtype.toAlgHom B.subtype.toAlgHom
    (fun a b ↦ hAB a b)
  map_star' x := by
    change
      Algebra.TensorProduct.lift A.subtype.toAlgHom B.subtype.toAlgHom
          (fun a b ↦ hAB a b) (star x) =
        star (Algebra.TensorProduct.lift A.subtype.toAlgHom B.subtype.toAlgHom
          (fun a b ↦ hAB a b) x)
    induction x with
    | zero => simp
    | tmul a b =>
        change ((star a : A) : C) * ((star b : B) : C) =
          star ((a : C) * (b : C))
        rw [star_mul]
        exact (hAB (star a) (star b)).eq
    | add x y hx hy => simp only [star_add, map_add, hx, hy]

/-- The commuting multiplication map sends a pure tensor to the ambient product. -/
@[simp]
theorem commutingMulMap_tmul (A B : StarSubalgebra ℂ C)
    [Nontrivial C]
    (hAB : ∀ a : A, ∀ b : B, Commute (a : C) (b : C)) (a : A) (b : B) :
    commutingMulMap A B hAB (a ⊗ₜ[ℂ] b) = (a : C) * (b : C) :=
  rfl

/-- The underlying linear map of commuting multiplication is the standard product map on the
underlying submodules. -/
theorem commutingMulMap_toLinearMap (A B : StarSubalgebra ℂ C)
    [Nontrivial C]
    (hAB : ∀ a : A, ∀ b : B, Commute (a : C) (b : C)) :
    (commutingMulMap A B hAB).toLinearMap =
      Submodule.mulMap A.toSubmodule B.toSubmodule := by
  apply TensorProduct.ext'
  intro a b
  rfl

/-- The range of multiplication from two commuting unital star-subalgebras is their algebraic
join. -/
theorem commutingMulMap_range (A B : StarSubalgebra ℂ C)
    [Nontrivial C]
    (hAB : ∀ a : A, ∀ b : B, Commute (a : C) (b : C)) :
    StarAlgHom.range (commutingMulMap A B hAB) = A ⊔ B := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x with
    | zero => rw [map_zero]; exact (A ⊔ B).zero_mem
    | tmul a b =>
        change (a : C) * (b : C) ∈ A ⊔ B
        exact (A ⊔ B).mul_mem ((show A ≤ A ⊔ B from le_sup_left) a.2)
          ((show B ≤ A ⊔ B from le_sup_right) b.2)
    | add x y hx hy => rw [map_add]; exact (A ⊔ B).add_mem hx hy
  · refine sup_le ?_ ?_
    · intro x hx
      exact ⟨(⟨x, hx⟩ : A) ⊗ₜ[ℂ] (1 : B), by simp⟩
    · intro x hx
      exact ⟨(1 : A) ⊗ₜ[ℂ] (⟨x, hx⟩ : B), by simp⟩

/-- The underlying complex vector space of the join of two commuting unital star-subalgebras is
the span of products of elements from the two factors. -/
theorem sup_toSubmodule_eq_mul (A B : StarSubalgebra ℂ C)
    [Nontrivial C]
    (hAB : ∀ a : A, ∀ b : B, Commute (a : C) (b : C)) :
    (A ⊔ B).toSubmodule = A.toSubmodule * B.toSubmodule := by
  rw [← commutingMulMap_range A B hAB]
  change LinearMap.range (commutingMulMap A B hAB).toLinearMap = _
  rw [commutingMulMap_toLinearMap, Submodule.mulMap_range]

private noncomputable def tensorProductStarAlgEquiv
    {A B D E : Type*}
    [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
    [Ring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]
    [Ring D] [Algebra ℂ D] [StarRing D] [StarModule ℂ D]
    [Ring E] [Algebra ℂ E] [StarRing E] [StarModule ℂ E]
    (eA : A ≃⋆ₐ[ℂ] D) (eB : B ≃⋆ₐ[ℂ] E) :
    A ⊗[ℂ] B ≃⋆ₐ[ℂ] D ⊗[ℂ] E :=
  StarAlgEquiv.ofAlgEquiv
    (Algebra.TensorProduct.congr eA.toAlgEquiv eB.toAlgEquiv) fun x ↦ by
      induction x with
      | zero => simp
      | tmul a b =>
          simp only [TensorProduct.star_tmul, Algebra.TensorProduct.congr_apply,
            Algebra.TensorProduct.map_tmul]
          change eA (star a) ⊗ₜ[ℂ] eB (star b) = star (eA a) ⊗ₜ[ℂ] star (eB b)
          rw [map_star eA a, map_star eB b]
      | add x y hx hy => simp only [star_add, map_add, hx, hy]

private noncomputable def tensorProductFullMatrixStarAlgEquiv
    {A B : Type*}
    [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
    [Ring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]
    {p q : ℕ} (eA : A ≃⋆ₐ[ℂ] Matrix (Fin p) (Fin p) ℂ)
    (eB : B ≃⋆ₐ[ℂ] Matrix (Fin q) (Fin q) ℂ) :
    A ⊗[ℂ] B ≃⋆ₐ[ℂ] Matrix (Fin (p * q)) (Fin (p * q)) ℂ :=
  (tensorProductStarAlgEquiv eA eB).trans <|
    (Matrix.kroneckerStarAlgEquiv (Fin p) (Fin q) ℂ).trans <|
      Matrix.matrixReindexStarAlgEquiv finProdFinEquiv

section FullMatrix

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
variable (A B : StarSubalgebra ℂ (Matrix n n ℂ))
variable {p q : ℕ} [NeZero p] [NeZero q]

/-- For two commuting full matrix factors in a nonzero ambient matrix algebra, multiplication from
their tensor product is injective. This is the unital single-block specialization of
Schumacher--Werner Proposition `Cscom`, quant-ph/0405174, lines 2119--2138, used in GNVW at
arXiv:0910.3675v2, lines 1270--1308. -/
theorem commutingMulMap_injective_of_equiv_matrix
    (hAB : ∀ a : A, ∀ b : B, Commute (a : Matrix n n ℂ) (b : Matrix n n ℂ))
    (eA : A ≃⋆ₐ[ℂ] Matrix (Fin p) (Fin p) ℂ)
    (eB : B ≃⋆ₐ[ℂ] Matrix (Fin q) (Fin q) ℂ) :
    Function.Injective (commutingMulMap A B hAB) := by
  let hSimple : IsSimpleRing (A ⊗[ℂ] B) :=
    IsSimpleRing.of_ringEquiv
      (tensorProductFullMatrixStarAlgEquiv eA eB).symm.toRingEquiv inferInstance
  exact @RingHom.injective _ _ _ hSimple _ _ (commutingMulMap A B hAB).toRingHom

/-- The join of two commuting full matrix factors of sizes `p` and `q` is a full matrix algebra of
size `p * q`. This is the unital single-block specialization of Schumacher--Werner Proposition
`Cscom`, quant-ph/0405174, lines 2119--2138. It does not assert that the join is the whole ambient
matrix algebra. -/
noncomputable def commutingSupEquivMatrix
    (hAB : ∀ a : A, ∀ b : B, Commute (a : Matrix n n ℂ) (b : Matrix n n ℂ))
    (eA : A ≃⋆ₐ[ℂ] Matrix (Fin p) (Fin p) ℂ)
    (eB : B ≃⋆ₐ[ℂ] Matrix (Fin q) (Fin q) ℂ) :
    ↥(A ⊔ B) ≃⋆ₐ[ℂ] Matrix (Fin (p * q)) (Fin (p * q)) ℂ := by
  let eJoin : A ⊗[ℂ] B ≃⋆ₐ[ℂ] ↥(A ⊔ B) := by
    rw [← commutingMulMap_range A B hAB]
    exact StarAlgEquiv.ofInjective (commutingMulMap A B hAB)
      (commutingMulMap_injective_of_equiv_matrix A B hAB eA eB)
  exact eJoin.symm.trans (tensorProductFullMatrixStarAlgEquiv eA eB)

/-- The full-matrix presentation of the join of two commuting full matrix factors exists. -/
theorem nonempty_equiv_sup_matrix
    (hAB : ∀ a : A, ∀ b : B, Commute (a : Matrix n n ℂ) (b : Matrix n n ℂ))
    (eA : A ≃⋆ₐ[ℂ] Matrix (Fin p) (Fin p) ℂ)
    (eB : B ≃⋆ₐ[ℂ] Matrix (Fin q) (Fin q) ℂ) :
    Nonempty (↥(A ⊔ B) ≃⋆ₐ[ℂ] Matrix (Fin (p * q)) (Fin (p * q)) ℂ) :=
  ⟨commutingSupEquivMatrix A B hAB eA eB⟩

/-- The complex dimension of the join of commuting full matrix factors of sizes `p` and `q` is
`(p * q) * (p * q)`. -/
theorem finrank_sup_of_equiv_matrix
    (hAB : ∀ a : A, ∀ b : B, Commute (a : Matrix n n ℂ) (b : Matrix n n ℂ))
    (eA : A ≃⋆ₐ[ℂ] Matrix (Fin p) (Fin p) ℂ)
    (eB : B ≃⋆ₐ[ℂ] Matrix (Fin q) (Fin q) ℂ) :
    Module.finrank ℂ ↥(A ⊔ B) = (p * q) * (p * q) := by
  calc
    Module.finrank ℂ ↥(A ⊔ B) =
        Module.finrank ℂ (Matrix (Fin (p * q)) (Fin (p * q)) ℂ) :=
      (commutingSupEquivMatrix A B hAB eA eB).toAlgEquiv.toLinearEquiv.finrank_eq
    _ = (p * q) * (p * q) := by simp [Module.finrank_matrix]

end FullMatrix

end StarSubalgebra

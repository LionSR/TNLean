/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Matrix.PEquiv
import TNLean.Algebra.MatrixL2Contraction

/-!
# Kronecker products, relabellings and the `L²` operator norm

Elementary facts about Kronecker products of complex matrices and vectors, and about relabelling
their coordinates along equivalences, used when two copies of a system are rearranged.

## Main declarations

* `Matrix.kronecker_kronecker_eq_submatrix`: `(A₁ ⊗ B₁) ⊗ (A₂ ⊗ B₂)` is `(A₁ ⊗ A₂) ⊗ (B₁ ⊗ B₂)`
  in the coordinates `Equiv.prodProdProdComm`.
* `Matrix.l2_opNorm_kronecker_le`: `‖A ⊗ B‖ ≤ ‖A‖ ‖B‖`.
* `Matrix.l2_opNorm_toMatrix_toPEquiv_le`: the matrix of a bijection of coordinates is a
  contraction.
* `Matrix.norm_submatrix_equiv_le`, `Commute.submatrix_equiv`: relabelling both coordinates of a
  square matrix along one equivalence.
* `EuclideanSpace.vecKron`, `EuclideanSpace.norm_vecKron`: the product vector `x ⊗ y` and
  `‖x ⊗ y‖ = ‖x‖ ‖y‖`.
-/

open scoped Kronecker Matrix.Norms.L2Operator

namespace Matrix

section Shuffle

variable {α β γ δ α' β' γ' δ' : Type*}

/-- `(A₁ ⊗ B₁) ⊗ (A₂ ⊗ B₂)` is `(A₁ ⊗ A₂) ⊗ (B₁ ⊗ B₂)` in shuffled coordinates. -/
theorem kronecker_kronecker_eq_submatrix (A₁ : Matrix α α' ℂ) (B₁ : Matrix β β' ℂ)
    (A₂ : Matrix γ γ' ℂ) (B₂ : Matrix δ δ' ℂ) :
    (A₁ ⊗ₖ B₁) ⊗ₖ (A₂ ⊗ₖ B₂) =
      ((A₁ ⊗ₖ A₂) ⊗ₖ (B₁ ⊗ₖ B₂)).submatrix (Equiv.prodProdProdComm α β γ δ)
        (Equiv.prodProdProdComm α' β' γ' δ') := by
  ext ⟨⟨a, b⟩, ⟨c, d⟩⟩ ⟨⟨a', b'⟩, ⟨c', d'⟩⟩
  simp only [kroneckerMap_apply, submatrix_apply, Equiv.prodProdProdComm, Equiv.coe_fn_mk]
  ring

end Shuffle

section Norms

variable {m n m' n' : Type*} [Fintype m] [Fintype n] [Fintype m'] [Fintype n'] [DecidableEq m]
  [DecidableEq n] [DecidableEq m'] [DecidableEq n']

omit [DecidableEq m'] in
/-- `‖1 ⊗ B‖ ≤ ‖B‖`. -/
theorem l2_opNorm_one_kronecker_le (B : Matrix m' n ℂ) :
    ‖(1 : Matrix m m ℂ) ⊗ₖ B‖ ≤ ‖B‖ := by
  have h : (1 : Matrix m m ℂ) ⊗ₖ B =
      reindex (Equiv.prodComm m' m) (Equiv.prodComm n m) (B ⊗ₖ (1 : Matrix m m ℂ)) := by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp [kroneckerMap_apply, mul_comm]
  rw [h]
  exact (l2_opNorm_reindex_le _ _ _).trans (l2_opNorm_kronecker_one_le B)

omit [DecidableEq m'] [DecidableEq n'] in
/-- `‖A ⊗ B‖ ≤ ‖A‖ ‖B‖`. -/
theorem l2_opNorm_kronecker_le (A : Matrix m' m ℂ) (B : Matrix n' n ℂ) :
    ‖A ⊗ₖ B‖ ≤ ‖A‖ * ‖B‖ := by
  classical
  have h : A ⊗ₖ B = (A ⊗ₖ (1 : Matrix n' n' ℂ)) * ((1 : Matrix m m ℂ) ⊗ₖ B) := by
    rw [← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  rw [h]
  exact (l2_opNorm_mul _ _).trans (mul_le_mul (l2_opNorm_kronecker_one_le A)
    (l2_opNorm_one_kronecker_le B) (norm_nonneg _) (norm_nonneg _))

omit [DecidableEq m'] [DecidableEq n'] in
/-- The Kronecker product of two contractions is a contraction. -/
theorem l2_opNorm_kronecker_le_one {A : Matrix m' m ℂ} {B : Matrix n' n ℂ} (hA : ‖A‖ ≤ 1)
    (hB : ‖B‖ ≤ 1) : ‖A ⊗ₖ B‖ ≤ 1 :=
  (l2_opNorm_kronecker_le A B).trans (by nlinarith [norm_nonneg A, norm_nonneg B])

omit [DecidableEq m] in
/-- The matrix of a bijection of coordinates is a contraction. -/
theorem l2_opNorm_toMatrix_toPEquiv_le (f : m ≃ n) :
    ‖(f.toPEquiv.toMatrix : Matrix m n ℂ)‖ ≤ 1 := by
  have h : (f.toPEquiv.toMatrix : Matrix m n ℂ) = reindex f.symm (Equiv.refl n) 1 := by
    rw [← Matrix.mul_one (f.toPEquiv.toMatrix : Matrix m n ℂ), PEquiv.toMatrix_toPEquiv_mul]
    rfl
  rw [h]
  exact (l2_opNorm_reindex_le _ _ _).trans (IsStarProjection.one _).norm_le

/-- Relabelling both coordinates of a square matrix along one equivalence does not increase
the operator norm. -/
theorem norm_submatrix_equiv_le (M : Matrix n n ℂ) (e : m ≃ n) : ‖M.submatrix e e‖ ≤ ‖M‖ :=
  l2_opNorm_reindex_le e.symm e.symm M

end Norms

section Relabel

variable {m n m' n' : Type*}

/-- The matrix of a product of bijections is the Kronecker product of their matrices. -/
theorem toMatrix_toPEquiv_prodCongr [DecidableEq m'] [DecidableEq n'] (f : m ≃ m')
    (g : n ≃ n') :
    ((f.prodCongr g).toPEquiv.toMatrix : Matrix (m × n) (m' × n') ℂ) =
      (f.toPEquiv.toMatrix : Matrix m m' ℂ) ⊗ₖ (g.toPEquiv.toMatrix : Matrix n n' ℂ) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq,
    kroneckerMap_apply, Equiv.prodCongr_apply, Prod.map, Prod.mk.injEq]
  by_cases h₁ : f i = k <;> by_cases h₂ : g j = l <;> simp [h₁, h₂]

/-- Relabelling the coordinates of the matrix of a bijection. -/
theorem toMatrix_toPEquiv_submatrix [DecidableEq n] {l l' : Type*} [DecidableEq l'] (f : m ≃ n)
    (e₁ : l ≃ m) (e₂ : l' ≃ n) :
    (f.toPEquiv.toMatrix : Matrix m n ℂ).submatrix e₁ e₂ =
      ((e₁.trans (f.trans e₂.symm)).toPEquiv.toMatrix : Matrix l l' ℂ) := by
  ext i j
  simp only [submatrix_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Equiv.trans_apply,
    Option.mem_some_iff, Equiv.symm_apply_eq]

/-- Relabelling along `e` and then along `e.symm` is the identity. -/
theorem submatrix_symm_submatrix (X : Matrix n n ℂ) (e : m ≃ n) :
    (X.submatrix e e).submatrix e.symm e.symm = X := by
  simp [submatrix_submatrix]

end Relabel

end Matrix

/-- Commuting square matrices commute in all coordinates. -/
theorem Commute.submatrix_equiv {m n : Type*} [Fintype m] [Fintype n] {X Y : Matrix n n ℂ}
    (h : Commute X Y) (e : m ≃ n) : Commute (X.submatrix e e) (Y.submatrix e e) := by
  change X.submatrix e e * Y.submatrix e e = Y.submatrix e e * X.submatrix e e
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h.eq]

namespace EuclideanSpace

variable {m n : Type*}

/-- Relabelling the coordinates of a vector does not change its norm. -/
theorem norm_toLp_comp_equiv [Fintype m] [Fintype n] (e : m ≃ n) (f : n → ℂ) :
    ‖(WithLp.toLp 2 (f ∘ e) : EuclideanSpace ℂ m)‖ = ‖(WithLp.toLp 2 f : EuclideanSpace ℂ n)‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  exact e.sum_comp fun j => ‖f j‖ ^ 2

/-- The product vector `x ⊗ y`. -/
noncomputable def vecKron (x : EuclideanSpace ℂ m) (y : EuclideanSpace ℂ n) :
    EuclideanSpace ℂ (m × n) :=
  WithLp.toLp 2 fun p => x p.1 * y p.2

theorem vecKron_sub_left (x x' : EuclideanSpace ℂ m) (y : EuclideanSpace ℂ n) :
    vecKron x y - vecKron x' y = vecKron (x - x') y := by
  ext ⟨i, j⟩
  simp [vecKron, sub_mul]

theorem vecKron_sub_right (x : EuclideanSpace ℂ m) (y y' : EuclideanSpace ℂ n) :
    vecKron x y - vecKron x y' = vecKron x (y - y') := by
  ext ⟨i, j⟩
  simp [vecKron, mul_sub]

variable [Fintype m] [Fintype n]

/-- `‖x ⊗ y‖ = ‖x‖ ‖y‖`. -/
theorem norm_vecKron (x : EuclideanSpace ℂ m) (y : EuclideanSpace ℂ n) :
    ‖vecKron x y‖ = ‖x‖ * ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← Real.sqrt_mul
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  congr 1
  simp only [vecKron, Fintype.sum_prod_type, norm_mul, mul_pow, Finset.sum_mul_sum]

/-- `‖x ⊗ x - y ⊗ y‖ ≤ ‖x - y‖ (‖x‖ + ‖y‖)`. -/
theorem norm_vecKron_self_sub_le (x y : EuclideanSpace ℂ m) :
    ‖vecKron x x - vecKron y y‖ ≤ ‖x - y‖ * (‖x‖ + ‖y‖) := by
  have h : vecKron x x - vecKron y y = vecKron (x - y) x + vecKron y (x - y) := by
    rw [← vecKron_sub_left, ← vecKron_sub_right]
    abel
  rw [h]
  refine (norm_add_le _ _).trans ?_
  rw [norm_vecKron, norm_vecKron]
  linarith [mul_comm ‖y‖ ‖x - y‖]

end EuclideanSpace

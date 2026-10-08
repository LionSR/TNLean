/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixAux
import QICLean.Analysis.MatrixFramePerturbation
import QICLean.Analysis.RootChannel

/-!
# Contractions in the `L²` operator norm

Elementary facts about complex matrices of operator norm at most one, for rectangular matrices
indexed by arbitrary finite types: relabelling rows and columns and tensoring with an identity
do not increase the operator norm, a matrix whose Gram matrix is a contraction is a
contraction, and products of contractions are contractions.

## Main declarations

* `Matrix.l2_opNorm_reindex_le`: relabelling rows and columns of a rectangular matrix.
* `Matrix.l2_opNorm_le_one_of_conjTranspose_mul_self_le_one`: `‖Aᴴ A‖ ≤ 1` gives `‖A‖ ≤ 1`.
* `Matrix.IsIsometry.l2_opNorm_le_one`: an isometry is a contraction.
* `Matrix.l2_opNorm_mul_le_one`, `Matrix.l2_opNorm_list_prod_le_one`: products of contractions.
* `Matrix.l2_opNorm_conjTranspose_mul_mul_le_one`: `‖Aᴴ F A‖ ≤ 1` for contractions `A` and `F`.
* `Matrix.kronecker_one_mul_apply`: the entries of `(N ⊗ 1) C` on one identity slice.
-/

open scoped Kronecker Matrix.Norms.L2Operator

namespace Matrix

variable {m n m' n' : Type*} [Fintype m] [Fintype n] [Fintype m'] [Fintype n'] [DecidableEq n]
  [DecidableEq n']

/-- Relabelling the rows and the columns of a rectangular matrix does not increase its operator
norm. -/
theorem l2_opNorm_reindex_le (e : m ≃ m') (f : n ≃ n') (A : Matrix m n ℂ) :
    ‖reindex e f A‖ ≤ ‖A‖ := by
  refine l2_opNorm_le_of_forall (norm_nonneg _) fun v => ?_
  have h := A.l2_opNorm_mulVec (WithLp.toLp 2 fun j => v (f j))
  have hv : ‖(WithLp.toLp 2 fun j => v (f j) : EuclideanSpace ℂ n)‖ =
      ‖(EuclideanSpace.equiv n' ℂ).symm v‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    exact Equiv.sum_comp f (fun j => ‖v j‖ ^ 2)
  have hA : ‖(EuclideanSpace.equiv m' ℂ).symm (reindex e f A *ᵥ v)‖ =
      ‖(WithLp.toLp 2 (A *ᵥ fun j => v (f j)) : EuclideanSpace ℂ m)‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    refine (Equiv.sum_comp e fun i' => ‖(reindex e f A *ᵥ v) i'‖ ^ 2).symm.trans ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [reindex_apply, mulVec, dotProduct, submatrix_apply]
    congr 2
    rw [← Equiv.sum_comp f]
    simp
  rw [hA, ← hv]
  exact h

/-- A matrix whose Gram matrix has operator norm at most one is a contraction. -/
theorem l2_opNorm_le_one_of_conjTranspose_mul_self_le_one {A : Matrix m n ℂ}
    (h : ‖Aᴴ * A‖ ≤ 1) : ‖A‖ ≤ 1 := by
  rw [l2_opNorm_conjTranspose_mul_self] at h
  nlinarith [norm_nonneg A]

/-- An isometry `Aᴴ A = 1` is a contraction. -/
theorem IsIsometry.l2_opNorm_le_one {A : Matrix m n ℂ} (hA : A.IsIsometry) : ‖A‖ ≤ 1 :=
  l2_opNorm_le_one_of_conjTranspose_mul_self_le_one (by
    rw [show Aᴴ * A = 1 from hA]; exact (IsStarProjection.one _).norm_le)

/-- The product of two contractions is a contraction. -/
theorem l2_opNorm_mul_le_one {l : Type*} [Fintype l] [DecidableEq l] {A : Matrix m n ℂ}
    {B : Matrix n l ℂ} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) : ‖A * B‖ ≤ 1 :=
  (l2_opNorm_mul A B).trans ((mul_le_mul hA hB (norm_nonneg B) zero_le_one).trans_eq (one_mul 1))

/-- Compressing a contraction `F` by a contraction `A` gives a contraction `Aᴴ F A`. -/
theorem l2_opNorm_conjTranspose_mul_mul_le_one [DecidableEq m] {A : Matrix m n ℂ}
    {F : Matrix m m ℂ} (hA : ‖A‖ ≤ 1) (hF : ‖F‖ ≤ 1) : ‖Aᴴ * F * A‖ ≤ 1 :=
  l2_opNorm_mul_le_one (l2_opNorm_mul_le_one (by rwa [l2_opNorm_conjTranspose]) hF) hA

/-- The product of a list of contractions is a contraction. -/
theorem l2_opNorm_list_prod_le_one :
    (l : List (Matrix n n ℂ)) → (∀ A ∈ l, ‖A‖ ≤ 1) → ‖l.prod‖ ≤ 1
  | [], _ => (IsStarProjection.one (Matrix n n ℂ)).norm_le
  | A :: l, h => by
    rw [List.prod_cons]
    exact l2_opNorm_mul_le_one (h A List.mem_cons_self)
      (l2_opNorm_list_prod_le_one l fun B hB => h B (List.mem_cons_of_mem _ hB))

end Matrix

/-- The entries of `(N ⊗ 1) C` on the identity slice `u` are those of `N` times the slice of
`C` at `u`. -/
theorem Matrix.kronecker_one_mul_apply {α m n l κ : Type*} [NonAssocSemiring α] [Fintype n]
    [Fintype κ] [DecidableEq κ] (N : Matrix m n α) (C : Matrix (n × κ) l α) (r : m) (u : κ)
    (τ : l) :
    ((N ⊗ₖ (1 : Matrix κ κ α)) * C) (r, u) τ = (N * Matrix.of fun s τ => C (s, u) τ) r τ := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply]

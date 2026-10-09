/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixAux
import QICLean.Analysis.MatrixFramePerturbation
import QICLean.Analysis.RectangularTraceNorm
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
* `Matrix.l2_opNorm_list_prod_le_one`: finite products of contractions, using QICLean's
  `Matrix.l2_opNorm_mul_le_one` for two factors.
* `Matrix.l2_opNorm_conjTranspose_mul_mul_le_one`: `‖Aᴴ F A‖ ≤ 1` for contractions `A` and `F`.
* `Matrix.l2_opNorm_le_of_blocks`: the operator norm of a block-diagonal matrix is at most the
  largest Hilbert--Schmidt norm of its diagonal blocks.
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

/-- Compressing a contraction `F` by a contraction `A` gives a contraction `Aᴴ F A`. -/
theorem l2_opNorm_conjTranspose_mul_mul_le_one [DecidableEq m] {A : Matrix m n ℂ}
    {F : Matrix m m ℂ} (hA : ‖A‖ ≤ 1) (hF : ‖F‖ ≤ 1) : ‖Aᴴ * F * A‖ ≤ 1 :=
  l2_opNorm_mul_le_one _ _ (l2_opNorm_mul_le_one _ _ (by rwa [l2_opNorm_conjTranspose]) hF) hA

/-- The product of a list of contractions is a contraction. -/
theorem l2_opNorm_list_prod_le_one :
    (l : List (Matrix n n ℂ)) → (∀ A ∈ l, ‖A‖ ≤ 1) → ‖l.prod‖ ≤ 1
  | [], _ => (IsStarProjection.one (Matrix n n ℂ)).norm_le
  | A :: l, h => by
    rw [List.prod_cons]
    exact l2_opNorm_mul_le_one _ _ (h A List.mem_cons_self)
      (l2_opNorm_list_prod_le_one l fun B hB => h B (List.mem_cons_of_mem _ hB))

/-- **Block-diagonal operator norm.** If `Y a b` vanishes unless the labels `u a` and `u' b`
agree, then the operator norm of `Y` is at most the largest Hilbert--Schmidt norm of its diagonal
blocks. -/
theorem l2_opNorm_le_of_blocks {α β U : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    [Finite U] [DecidableEq U] (Y : Matrix α β ℂ) (u : α → U) (u' : β → U)
    (hY : ∀ a b, u a ≠ u' b → Y a b = 0) {c : ℝ} (hc : 0 ≤ c)
    (hblock : ∀ z, ∑ a ∈ Finset.univ.filter (u · = z),
      ∑ b ∈ Finset.univ.filter (u' · = z), ‖Y a b‖ ^ 2 ≤ c ^ 2) :
    ‖Y‖ ≤ c := by
  have := Fintype.ofFinite U
  refine l2_opNorm_le_of_forall hc fun v => ?_
  set F : U → ℝ := fun z => ∑ b ∈ Finset.univ.filter (u' · = z), ‖v b‖ ^ 2
  have hrow : ∀ a, ‖(Y *ᵥ v) a‖ ^ 2 ≤
      (∑ b ∈ Finset.univ.filter (u' · = u a), ‖Y a b‖ ^ 2) * F (u a) := by
    intro a
    have hsum : (Y *ᵥ v) a = ∑ b ∈ Finset.univ.filter (u' · = u a), Y a b * v b := by
      rw [mulVec, dotProduct, Finset.sum_filter]
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs with h
      · rfl
      · rw [hY a b (Ne.symm h), zero_mul]
    rw [hsum]
    calc ‖∑ b ∈ Finset.univ.filter (u' · = u a), Y a b * v b‖ ^ 2
        ≤ (∑ b ∈ Finset.univ.filter (u' · = u a), ‖Y a b‖ * ‖v b‖) ^ 2 := by
          gcongr
          exact (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun b _ => norm_mul _ _)
      _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hv : ‖(EuclideanSpace.equiv β ℂ).symm v‖ ^ 2 = ∑ z, F z := by
    rw [EuclideanSpace.norm_sq_eq, Finset.sum_fiberwise]
    rfl
  have hYv : ‖(EuclideanSpace.equiv α ℂ).symm (Y *ᵥ v)‖ ^ 2 ≤
      (c * ‖(EuclideanSpace.equiv β ℂ).symm v‖) ^ 2 := by
    rw [mul_pow, hv, Finset.mul_sum, EuclideanSpace.norm_sq_eq]
    calc ∑ a, ‖(EuclideanSpace.equiv α ℂ).symm (Y *ᵥ v) a‖ ^ 2
        ≤ ∑ a, (∑ b ∈ Finset.univ.filter (u' · = u a), ‖Y a b‖ ^ 2) * F (u a) :=
          Finset.sum_le_sum fun a _ => hrow a
      _ = ∑ z, ∑ a ∈ Finset.univ.filter (u · = z),
            (∑ b ∈ Finset.univ.filter (u' · = z), ‖Y a b‖ ^ 2) * F z := by
          rw [← Finset.sum_fiberwise Finset.univ u]
          refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun a ha => ?_
          rw [(Finset.mem_filter.mp ha).2]
      _ ≤ ∑ z, c ^ 2 * F z := by
          refine Finset.sum_le_sum fun z _ => ?_
          rw [← Finset.sum_mul]
          exact mul_le_mul_of_nonneg_right (hblock z)
            (Finset.sum_nonneg fun b _ => sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hYv

end Matrix

/-- The entries of `(N ⊗ 1) C` on the identity slice `u` are those of `N` times the slice of
`C` at `u`. -/
theorem Matrix.kronecker_one_mul_apply {α m n l κ : Type*} [NonAssocSemiring α] [Fintype n]
    [Fintype κ] [DecidableEq κ] (N : Matrix m n α) (C : Matrix (n × κ) l α) (r : m) (u : κ)
    (τ : l) :
    ((N ⊗ₖ (1 : Matrix κ κ α)) * C) (r, u) τ = (N * Matrix.of fun s τ => C (s, u) τ) r τ := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply]

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Topology.Instances.Matrix
import QICLean.Algebra.OperatorSchmidtRealignment
import TNLean.Algebra.RankOneFactorization

/-!
# Realignment of a bipartite matrix

The realignment of a matrix `M` on a product index pairs the two indices of each
tensor factor: the entry `M (i, k) (i', k')` becomes the entry at row `(i, i')`
and column `(k, k')`. It sends a Kronecker product `A ⊗ B` to the outer product
of the entry vectors of `A` and `B`, and left multiplication by a product
`h ⊗ k` to multiplication by `h ⊗ 1` on the left and by `(k ⊗ 1)ᵀ` on the right.
The realignment has rank one exactly when `M` is the Kronecker product of two
nonzero factors.

This is step 1 of the cross-section construction that replaces the slice theorem
of Montgomery and Yang in arXiv:1703.09188, proof of Corollary `coruvSF`,
lines 942--947 (see `docs/paper-gaps/mpu_standard_form_path_cross_section.tex`).
For square factors the rank of the realignment is the operator Schmidt rank
(`Matrix.operatorSchmidtRank_eq_rank_realign`).

## Main declarations

* `Matrix.realign`: the realignment, with inverse `Matrix.unrealign`, packaged as
  the linear equivalence `Matrix.realignLinearEquiv`.
* `Matrix.realign_kronecker`: the realignment of `A ⊗ B` is the outer product of
  the entry vectors.
* `Matrix.realign_kronecker_mul`: equivariance under left multiplication by a
  Kronecker product.
* `Matrix.rank_realign_eq_one_iff`: the realignment has rank one if and only if
  the matrix is a Kronecker product of nonzero factors.
-/

open scoped Kronecker

namespace Matrix

variable {R m n m' n' m₂ n₂ : Type*}

/-- The realignment of a bipartite matrix: the entry `M (i, k) (i', k')` is
placed at row `(i, i')` and column `(k, k')`. It sends `A ⊗ B` to the outer
product of the entry vectors of `A` and `B` (`Matrix.realign_kronecker`).

Source: the realignment `R` of step 1 of the cross-section construction for
arXiv:1703.09188, Corollary `coruvSF`, lines 942--947. -/
def realign (M : Matrix (m × n) (m' × n') R) : Matrix (m × m') (n × n') R :=
  fun ij kl ↦ M (ij.1, kl.1) (ij.2, kl.2)

/-- The inverse of the realignment: the entry `N (i, i') (k, k')` is placed at
row `(i, k)` and column `(i', k')`.

Source: inverse of the realignment of the cross-section construction for
arXiv:1703.09188, Corollary `coruvSF`, lines 942--947. -/
def unrealign (N : Matrix (m × m') (n × n') R) : Matrix (m × n) (m' × n') R :=
  fun ik ik' ↦ N (ik.1, ik'.1) (ik.2, ik'.2)

@[simp]
theorem realign_apply (M : Matrix (m × n) (m' × n') R) (i : m) (i' : m') (k : n) (k' : n') :
    realign M (i, i') (k, k') = M (i, k) (i', k') :=
  rfl

@[simp]
theorem unrealign_apply (N : Matrix (m × m') (n × n') R) (i : m) (i' : m') (k : n) (k' : n') :
    unrealign N (i, k) (i', k') = N (i, i') (k, k') :=
  rfl

@[simp]
theorem unrealign_realign (M : Matrix (m × n) (m' × n') R) : unrealign (realign M) = M :=
  rfl

@[simp]
theorem realign_unrealign (N : Matrix (m × m') (n × n') R) : realign (unrealign N) = N :=
  rfl

/-- The realignment as a linear equivalence.

Source: the linear realignment of the cross-section construction for
arXiv:1703.09188, Corollary `coruvSF`, lines 942--947. -/
def realignLinearEquiv (R : Type*) [Semiring R] :
    Matrix (m × n) (m' × n') R ≃ₗ[R] Matrix (m × m') (n × n') R where
  toFun := realign
  invFun := unrealign
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv := unrealign_realign
  right_inv := realign_unrealign

@[simp]
theorem realignLinearEquiv_apply [Semiring R] (M : Matrix (m × n) (m' × n') R) :
    realignLinearEquiv R M = realign M :=
  rfl

@[simp]
theorem realignLinearEquiv_symm_apply [Semiring R] (N : Matrix (m × m') (n × n') R) :
    (realignLinearEquiv R).symm N = unrealign N :=
  rfl

/-- The realignment is continuous. -/
theorem continuous_realign [TopologicalSpace R] :
    Continuous (realign : Matrix (m × n) (m' × n') R → Matrix (m × m') (n × n') R) :=
  continuous_pi fun _ ↦ continuous_pi fun _ ↦ continuous_apply_apply _ _

/-- The inverse realignment is continuous. -/
theorem continuous_unrealign [TopologicalSpace R] :
    Continuous (unrealign : Matrix (m × m') (n × n') R → Matrix (m × n) (m' × n') R) :=
  continuous_pi fun _ ↦ continuous_pi fun _ ↦ continuous_apply_apply _ _

/-- **Realignment of a Kronecker product.** The realignment of `A ⊗ B` is the
outer product of the entry vectors of `A` and `B`.

Source: the identity `R(A ⊗ B) = vec A (vec B)ᵀ` of step 1 of the cross-section
construction for arXiv:1703.09188, Corollary `coruvSF`, lines 942--947. -/
theorem realign_kronecker [Mul R] (A : Matrix m m' R) (B : Matrix n n' R) :
    realign (A ⊗ₖ B) = vecMulVec (fun p ↦ A p.1 p.2) (fun p ↦ B p.1 p.2) := by
  ext ⟨i, i'⟩ ⟨k, k'⟩
  simp [vecMulVec_apply]

/-- **Equivariance of the realignment.** Left multiplication of `M` by `h ⊗ k`
becomes left multiplication of the realignment by `h ⊗ 1` and right
multiplication by `(k ⊗ 1)ᵀ`.

Source: the identity `R((h ⊗ k) M) = L_h R(M) L_kᵀ` of step 1 of the
cross-section construction for arXiv:1703.09188, Corollary `coruvSF`,
lines 942--947. -/
theorem realign_kronecker_mul [CommSemiring R] [Fintype m] [Fintype n] [Fintype m']
    [Fintype n'] [DecidableEq m'] [DecidableEq n']
    (h : Matrix m₂ m R) (k : Matrix n₂ n R) (M : Matrix (m × n) (m' × n') R) :
    realign ((h ⊗ₖ k) * M) =
      (h ⊗ₖ (1 : Matrix m' m' R)) * realign M * (k ⊗ₖ (1 : Matrix n' n' R))ᵀ := by
  ext ⟨i, i'⟩ ⟨j, j'⟩
  simp only [mul_apply, kroneckerMap_apply, transpose_apply,
    Fintype.sum_prod_type, one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.sum_mul, realign]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
  ring

/-- The rank of the realignment of a square bipartite matrix is its operator
Schmidt rank. -/
theorem operatorSchmidtRank_eq_rank_realign [Field R] [Fintype m] [Fintype n]
    (M : Matrix (m × n) (m × n) R) :
    operatorSchmidtRank M = (realign M).rank :=
  operatorSchmidtRank_eq_rank_realignment M

/-- An outer product of two nonzero vectors has rank one. -/
theorem rank_vecMulVec_eq_one [Field R] [Finite m] [Fintype n] {w : m → R} {v : n → R}
    (hw : w ≠ 0) (hv : v ≠ 0) : (vecMulVec w v).rank = 1 := by
  have := Fintype.ofFinite m
  refine le_antisymm (rank_vecMulVec_le w v) (Nat.one_le_iff_ne_zero.mpr fun h0 ↦ ?_)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  rw [rank_eq_finrank_span_cols, Submodule.finrank_eq_zero] at h0
  have hcol : (vecMulVec w v).col j ∈ Submodule.span R (Set.range (vecMulVec w v).col) :=
    Submodule.subset_span ⟨j, rfl⟩
  rw [h0, Submodule.mem_bot] at hcol
  have := congrFun hcol i
  simp only [col_apply, vecMulVec_apply, Pi.zero_apply, mul_eq_zero] at this
  exact this.elim hi hj

/-- **Rank-one realignments are Kronecker products.** The realignment of `M`
has rank one if and only if `M` is the Kronecker product of two nonzero
matrices.

Source: the rank-one characterization of step 1 of the cross-section
construction for arXiv:1703.09188, Corollary `coruvSF`, lines 942--947. -/
theorem rank_realign_eq_one_iff [Field R] [Finite m] [Fintype n] [Finite m'] [Fintype n']
    (M : Matrix (m × n) (m' × n') R) :
    (realign M).rank = 1 ↔
      ∃ (A : Matrix m m' R) (B : Matrix n n' R), A ≠ 0 ∧ B ≠ 0 ∧ M = A ⊗ₖ B := by
  constructor
  · intro h
    obtain ⟨w, v, hw, hv, hM⟩ := (realign M).exists_eq_vecMulVec_of_rank_eq_one h
    refine ⟨fun i i' ↦ w (i, i'), fun k k' ↦ v (k, k'), fun h0 ↦ hw ?_, fun h0 ↦ hv ?_, ?_⟩
    · funext p
      exact congrFun (congrFun h0 p.1) p.2
    · funext p
      exact congrFun (congrFun h0 p.1) p.2
    · rw [← unrealign_realign M, hM]
      ext ⟨i, k⟩ ⟨i', k'⟩
      rfl
  · rintro ⟨A, B, hA, hB, rfl⟩
    rw [realign_kronecker]
    refine rank_vecMulVec_eq_one (fun h0 ↦ hA ?_) (fun h0 ↦ hB ?_)
    · ext i i'
      exact congrFun h0 (i, i')
    · ext k k'
      exact congrFun h0 (k, k')

end Matrix

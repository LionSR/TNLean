/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CyclicActiveAreaLaw

/-!
# A non-Cartesian four-sector tensor

This file introduces a four-sector diagonal MPO tensor whose closed left and
right factors are
\[
 L=\begin{pmatrix}1&1&1&1\\1&2&-7&4\end{pmatrix},\qquad
 R=\begin{pmatrix}
 \frac14&-\frac3{100}\\
 \frac14&-\frac1{100}\\
 \frac14& \frac1{100}\\
 \frac14& \frac3{100}
 \end{pmatrix}.
\]
The product \(LR\) is the rank-one projection
\(\operatorname{diag}(1,0)\), whereas the opposite product \(T=RL\) is
strictly positive and satisfies \(T^2=T^3\) but not \(T^2=T\).  The four
matrices \(l_k r_k\) span the full two-by-two matrix algebra.

Unlike the earlier active-sector witness, the selected projective left and
right factors are pairwise distinct, as is immediate from the second row of
\(L\) and the second column of \(R\).  Thus the displayed sectors do not arise
from a Cartesian product of two binary coordinates.  The statements in this
file establish the finite-dimensional algebraic data only; they do not yet
assert that every physical-sector factorization retains these four sectors.

This construction concerns the gap in arXiv:1606.00608, Appendix C.2,
Proposition `prop2to3`, lines 1740--1782.
-/

open scoped Matrix BigOperators ComplexOrder Matrix.Norms.Operator

noncomputable section

namespace MPOTensor.NonCartesianActiveSectorCandidate

/-- The closed left-sector vectors. -/
def leftPairing : Matrix (Fin 2) (Fin 4) ℂ :=
  !![1, 1, 1, 1;
     1, 2, -7, 4]

/-- The closed right-sector functionals. -/
def rightPairing : Matrix (Fin 4) (Fin 2) ℂ :=
  !![1 / 4, -3 / 100;
     1 / 4, -1 / 100;
     1 / 4,  1 / 100;
     1 / 4,  3 / 100]

/-- The virtual matrix attached to a scalar physical sector. -/
def sectorMatrix (k : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.vecMulVec (fun beta ↦ leftPairing beta k)
    (fun alpha ↦ rightPairing k alpha)

/-- The diagonal physical tensor formed from the four sector matrices. -/
def tensor : MPOTensor 4 2 :=
  fun i j ↦ if i = j then sectorMatrix i else 0

/-- Closing the four physical sectors gives the rank-one projection
`diag(1,0)`. -/
lemma leftPairing_mul_rightPairing :
    leftPairing * rightPairing = !![1, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leftPairing, rightPairing, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

/-- The neighboring trace matrix of the displayed scalar-sector
factorization. -/
def traceMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![11 / 50, 19 / 100, 23 / 50, 13 / 100;
      6 / 25, 23 / 100,  8 / 25, 21 / 100;
     13 / 50, 27 / 100,  9 / 50, 29 / 100;
      7 / 25, 31 / 100,  1 / 25, 37 / 100]

/-- The opposite rectangular product is the complexification of the real
trace matrix. -/
lemma rightPairing_mul_leftPairing :
    rightPairing * leftPairing = Matrix.map traceMatrix Complex.ofReal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [leftPairing, rightPairing, traceMatrix,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Every neighboring trace coefficient is strictly positive. -/
lemma traceMatrix_pos (i j : Fin 4) : 0 < traceMatrix i j := by
  fin_cases i <;> fin_cases j <;> norm_num [traceMatrix]

/-- Every column of the neighboring trace matrix sums to one. -/
lemma traceMatrix_column_sum (j : Fin 4) : ∑ i, traceMatrix i j = 1 := by
  fin_cases j <;>
    norm_num [traceMatrix, Fin.sum_univ_four,
      Matrix.cons_val_two, Matrix.cons_val_three]

/-- Squaring the neighboring trace matrix removes its nilpotent part. -/
lemma traceMatrix_sq :
    traceMatrix ^ 2 = Matrix.of fun _ _ ↦ (1 / 4 : ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [traceMatrix, pow_two, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.cons_val_two, Matrix.cons_val_three]

/-- The neighboring trace matrix satisfies the square--cube relation. -/
lemma traceMatrix_sq_eq_cube : traceMatrix ^ 2 = traceMatrix ^ 3 := by
  rw [show traceMatrix ^ 3 = traceMatrix ^ 2 * traceMatrix by
    simp [pow_succ]]
  rw [traceMatrix_sq]
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply]
  rw [← Finset.mul_sum]
  norm_num [traceMatrix_column_sum]

/-- The neighboring trace matrix itself is not idempotent. -/
lemma traceMatrix_not_idempotent : traceMatrix ^ 2 ≠ traceMatrix := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  rw [traceMatrix_sq] at h01
  norm_num [traceMatrix] at h01

/-- The four sector matrices form a basis of the two-by-two matrix algebra. -/
lemma sectorMatrix_span_eq_top :
    Submodule.span ℂ (Set.range sectorMatrix) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro X
  let c : Fin 4 → ℂ :=
    ![X 0 0 - (145 / 3) * X 0 1 - (4 / 5) * X 1 0 + (50 / 3) * X 1 1,
      X 0 0 + 45 * X 0 1 + (7 / 5) * X 1 0 - 25 * X 1 1,
      X 0 0 + 5 * X 0 1 - (2 / 5) * X 1 0,
      X 0 0 - (5 / 3) * X 0 1 - (1 / 5) * X 1 0 + (25 / 3) * X 1 1]
  have hsum : X = ∑ k, c k • sectorMatrix k := by
    ext i j
    change X i j = ∑ k : Fin 4, c k * sectorMatrix k i j
    fin_cases i <;> fin_cases j <;>
      simp [c, sectorMatrix, leftPairing, rightPairing, Fin.sum_univ_four] <;>
      ring_nf
  rw [hsum]
  exact Submodule.sum_mem _ fun k _ ↦
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self k))

/-- The diagonal tensor is injective already at one site. -/
lemma tensor_isInjective : tensor.IsInjective := by
  apply top_unique
  rw [← sectorMatrix_span_eq_top]
  apply Submodule.span_le.2
  rintro _ ⟨k, rfl⟩
  apply Submodule.subset_span
  refine ⟨finProdFinEquiv (k, k), ?_⟩
  change tensor (finProdFinEquiv (k, k)).divNat
      (finProdFinEquiv (k, k)).modNat = sectorMatrix k
  rw [MPSTensor.finProdFinEquiv_divNat, MPSTensor.finProdFinEquiv_modNat]
  simp [tensor]

/-- The physical-trace transfer is the rectangular product \(LR\). -/
lemma physTraceTransfer_tensor :
    physTraceTransfer tensor = leftPairing * rightPairing := by
  ext i j
  change (∑ k : Fin 4, leftPairing i k * rightPairing k j) =
    ∑ k : Fin 4, leftPairing i k * rightPairing k j
  rfl

/-- The candidate tensor obeys literal physical-trace idempotence. -/
lemma physTraceTransfer_tensor_idempotent :
    physTraceTransfer tensor * physTraceTransfer tensor =
      physTraceTransfer tensor := by
  rw [physTraceTransfer_tensor, leftPairing_mul_rightPairing]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- Literal idempotence and nonvanishing give source zero correlation
length. -/
lemma tensor_isSourceZCL : tensor.IsSourceZCL := by
  apply isSourceZCL_of_physTraceTransfer_sq tensor
  · rw [physTraceTransfer_tensor, leftPairing_mul_rightPairing]
    intro h
    have h00 := congrFun (congrFun h 0) 0
    norm_num at h00
  · exact physTraceTransfer_tensor_idempotent

/-- The four-dimensional physical space as four scalar sectors. -/
def sectorEquiv : Fin 4 ≃ Σ _k : Fin 4, Fin 1 × Fin 1 where
  toFun k := ⟨k, (0, 0)⟩
  invFun q := q.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨k, ⟨x, y⟩⟩
    have hx : x = 0 := Subsingleton.elim _ _
    have hy : y = 0 := Subsingleton.elim _ _
    subst x
    subst y
    rfl

/-- The displayed scalar-sector factorization. -/
def factorization : PhysicalSectorFactorization tensor where
  sectorCount := 4
  leftDim := fun _ ↦ 1
  rightDim := fun _ ↦ 1
  leftDim_pos := fun _ ↦ by omega
  rightDim_pos := fun _ ↦ by omega
  sectorEquiv := sectorEquiv
  physicalIsometry := 1
  physicalIsometry_isometry := by simp
  leftTensor := fun k beta ↦ Matrix.of fun _ _ ↦ leftPairing beta k
  rightTensor := fun k alpha ↦ Matrix.of fun _ _ ↦ rightPairing k alpha
  factorization := by
    intro beta alpha
    ext q r
    obtain ⟨k, x, y⟩ := q
    obtain ⟨h, u, v⟩ := r
    fin_cases x
    fin_cases y
    fin_cases u
    fin_cases v
    by_cases hkh : k = h
    · subst h
      simp only [Matrix.reindex_apply, Matrix.conjTranspose_one, Matrix.one_mul,
        Matrix.mul_one]
      rw [Matrix.blockDiagonal'_apply_eq]
      simp [Matrix.submatrix_apply, sectorEquiv, physicalSlice, tensor,
        sectorMatrix]
      rfl
    · simp only [Matrix.reindex_apply, Matrix.conjTranspose_one,
        Matrix.one_mul, Matrix.mul_one]
      change tensor k h beta alpha =
        Matrix.blockDiagonal'
          (fun q ↦ Matrix.kroneckerMap (· * ·)
            (Matrix.of fun _ _ ↦ leftPairing beta q)
            (Matrix.of fun _ _ ↦ rightPairing q alpha))
          ⟨k, (0, 0)⟩ ⟨h, (0, 0)⟩
      rw [Matrix.blockDiagonal'_apply_ne _ _ _ hkh]
      simp [tensor, hkh]

/-- The neighboring operator of two scalar sectors is the corresponding
entry of the trace matrix. -/
lemma neighboringOperator_eq (k h : Fin 4) :
    factorization.neighboringOperator k h =
      Matrix.diagonal (fun _ : Fin 1 × Fin 1 ↦ (traceMatrix k h : ℂ)) := by
  ext x y
  obtain ⟨x₁, x₂⟩ := x
  obtain ⟨y₁, y₂⟩ := y
  fin_cases x₁
  fin_cases x₂
  fin_cases y₁
  fin_cases y₂
  simp only [PhysicalSectorFactorization.neighboringOperator_apply,
    factorization, Matrix.of_apply]
  change (∑ a, rightPairing k a * leftPairing a h) = (traceMatrix k h : ℂ)
  have hkh := congrFun (congrFun rightPairing_mul_leftPairing k) h
  simpa [Matrix.mul_apply] using hkh

/-- Every displayed neighboring operator is positive semidefinite. -/
lemma neighboringOperator_pos (k h : Fin 4) :
    (factorization.neighboringOperator k h).PosSemidef := by
  rw [neighboringOperator_eq]
  apply Matrix.PosSemidef.diagonal
  intro i
  change (0 : ℂ) ≤ (traceMatrix k h : ℂ)
  exact_mod_cast (traceMatrix_pos k h).le

/-- The candidate tensor satisfies saturation of the area law. -/
lemma tensor_isSAL : tensor.IsSAL := by
  let _ : NeZero 2 := ⟨by omega⟩
  exact factorization.isSAL_of_isSourceZCL tensor_isInjective
    neighboringOperator_pos tensor_isSourceZCL

end MPOTensor.NonCartesianActiveSectorCandidate

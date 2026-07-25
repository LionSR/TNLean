/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.PosSemidefSupport

/-!
# Rank-one eigenvector projections

This file gives the rank-one projection form of the standard finite-dimensional
spectral theorem for Hermitian matrices.  The projections are Hermitian,
positive semidefinite, idempotent, mutually orthogonal, and sum to the identity.
The matrix is their eigenvalue-weighted sum.

## Main declarations

* `Matrix.IsHermitian.eigenvectorProjection`: the projection onto one vector of
  the chosen orthonormal eigenbasis.
* `Matrix.IsHermitian.eigenvectorProjection_mul_eq_zero_of_ne`: projections
  associated with distinct basis vectors are orthogonal.
* `Matrix.IsHermitian.sum_eigenvectorProjection`: the eigenvector projections
  sum to the identity.
* `Matrix.IsHermitian.eq_sum_eigenvalues_smul_eigenvectorProjection`: the
  rank-one form of the finite-dimensional spectral theorem.
-/

open scoped Matrix ComplexOrder BigOperators

namespace Matrix.IsHermitian

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}

/-- The rank-one projection associated with one vector of the
orthonormal eigenbasis of a Hermitian matrix. -/
noncomputable def eigenvectorProjection (hA : A.IsHermitian) (k : n) : Matrix n n ℂ :=
  (hA.eigenvectorUnitary : Matrix n n ℂ) * Matrix.single k k 1 *
    star (hA.eigenvectorUnitary : Matrix n n ℂ)

/-- A rank-one eigenvector projection is the conjugate of a singleton diagonal
indicator by the eigenvector unitary. -/
theorem eigenvectorProjection_eq_indicator (hA : A.IsHermitian) (k : n) :
    hA.eigenvectorProjection k =
      (hA.eigenvectorUnitary : Matrix n n ℂ) *
        Matrix.diagonal (fun i => if i ∈ ({k} : Finset n) then (1 : ℂ) else 0) *
        star (hA.eigenvectorUnitary : Matrix n n ℂ) := by
  have hsingle :
      Matrix.single k k (1 : ℂ) =
        Matrix.diagonal (fun i => if i ∈ ({k} : Finset n) then (1 : ℂ) else 0) := by
    rw [← Matrix.diagonal_single]
    congr 1
    funext i
    simp [Pi.single_apply, eq_comm]
  rw [eigenvectorProjection, hsingle]

/-- A rank-one eigenvector projection is Hermitian. -/
theorem eigenvectorProjection_isHermitian (hA : A.IsHermitian) (k : n) :
    (hA.eigenvectorProjection k).IsHermitian := by
  rw [hA.eigenvectorProjection_eq_indicator k]
  exact hA.eigenvectorUnitary_indicator_isHermitian {k}

/-- A rank-one eigenvector projection is idempotent. -/
theorem eigenvectorProjection_idem (hA : A.IsHermitian) (k : n) :
    hA.eigenvectorProjection k * hA.eigenvectorProjection k = hA.eigenvectorProjection k := by
  rw [hA.eigenvectorProjection_eq_indicator k]
  exact hA.eigenvectorUnitary_indicator_idem {k}

/-- Projections associated with distinct eigenbasis vectors have zero product. -/
theorem eigenvectorProjection_mul_eq_zero_of_ne
    (hA : A.IsHermitian) {j k : n} (hjk : j ≠ k) :
    hA.eigenvectorProjection j * hA.eigenvectorProjection k = 0 := by
  set U := (hA.eigenvectorUnitary : Matrix n n ℂ)
  have hU : star U * U = 1 := by
    have hmem := hA.eigenvectorUnitary.2
    rw [Matrix.mem_unitaryGroup_iff'] at hmem
    exact hmem
  change
    (U * Matrix.single j j 1 * star U) * (U * Matrix.single k k 1 * star U) = 0
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star U) U, hU, Matrix.one_mul,
    ← Matrix.mul_assoc (Matrix.single j j 1) (Matrix.single k k 1),
    Matrix.single_mul_single_of_ne (c := (1 : ℂ)) j j k hjk (1 : ℂ),
    Matrix.zero_mul, Matrix.mul_zero]

/-- The rank-one eigenvector projections form a resolution of the identity. -/
theorem sum_eigenvectorProjection (hA : A.IsHermitian) :
    ∑ k, hA.eigenvectorProjection k = 1 := by
  let U := (hA.eigenvectorUnitary : Matrix n n ℂ)
  calc
    ∑ k, hA.eigenvectorProjection k =
        U * (∑ k : n, Matrix.single k k (1 : ℂ)) * star U := by
      simp [eigenvectorProjection, U, Finset.mul_sum, Finset.sum_mul]
    _ = U * 1 * star U := by rw [Matrix.sum_single_one]
    _ = 1 := by simp [U]

/-- The standard finite-dimensional spectral theorem in rank-one projection
form: a Hermitian matrix is the eigenvalue-weighted sum of its eigenvector
projections. -/
theorem eq_sum_eigenvalues_smul_eigenvectorProjection (hA : A.IsHermitian) :
    A = ∑ k, hA.eigenvalues k • hA.eigenvectorProjection k := by
  classical
  symm
  let U := (hA.eigenvectorUnitary : Matrix n n ℂ)
  have hdiag_sum :
      (∑ k : n, Matrix.single k k (hA.eigenvalues k : ℂ)) =
        Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
    rw [Matrix.sum_single_eq_diagonal]
    rfl
  have hterm :
      (∑ k, hA.eigenvalues k • hA.eigenvectorProjection k) =
        ∑ k : n, U * Matrix.single k k (hA.eigenvalues k : ℂ) * star U := by
    refine Finset.sum_congr rfl ?_
    intro k _
    change hA.eigenvalues k • (U * Matrix.single k k (1 : ℂ) * star U) =
      U * Matrix.single k k (hA.eigenvalues k : ℂ) * star U
    rw [← show hA.eigenvalues k • Matrix.single k k (1 : ℂ) =
        Matrix.single k k (hA.eigenvalues k : ℂ) by
          ext i j
          simp [Matrix.smul_apply, Matrix.single]]
    rw [Matrix.mul_smul, Matrix.smul_mul]
  calc
    (∑ k, hA.eigenvalues k • hA.eigenvectorProjection k) =
        ∑ k : n, U * Matrix.single k k (hA.eigenvalues k : ℂ) * star U := hterm
    _ = U * (∑ k : n, Matrix.single k k (hA.eigenvalues k : ℂ)) * star U := by
      rw [Matrix.mul_sum, Matrix.sum_mul]
    _ = U * Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U := by
      rw [hdiag_sum]
    _ = A := by
      simpa [U, Unitary.conjStarAlgAut_apply] using hA.spectral_theorem.symm

/-- On a finite coordinate space, every rank-one eigenvector projection is an
orthogonal projection. -/
theorem isOrthogonalProjection_eigenvectorProjection {D : ℕ}
    {A : Matrix (Fin D) (Fin D) ℂ} (hA : A.IsHermitian) (k : Fin D) :
    IsOrthogonalProjection (hA.eigenvectorProjection k) :=
  ⟨hA.eigenvectorProjection_isHermitian k, hA.eigenvectorProjection_idem k⟩

end Matrix.IsHermitian

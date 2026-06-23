/-
Copyright (c) 2026 Sirui Lu and TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Channel.SchmidtRank
import TNLean.Channel.Schwarz.TwoPositive

/-!
# Choi compression for the rank-one test

This file records the matrix identity connecting the pure-state ampliation test
for `k`-positivity with the Choi-matrix compression appearing in Wolf Chapter 3,
Proposition 3.1, equation (3.4).

The Choi matrix is normalized using `Matrix.omegaVec`, so the vector attached to
a matrix $X\in M_{D\times k}(\mathbb{C})$ has component $D^{-1/2}X_{i,p}$ at
the pair $(i,p)$.

## Main definitions

* `ChoiJamiolkowski.rightCompression`: the right-factor Choi compression,
  written in the index convention of the blockwise ampliation.
* `ChoiJamiolkowski.rightTensorMatrix`: the matrix form of the right tensor
  factor acting on the Choi auxiliary index.
* `ChoiJamiolkowski.compressedOmegaVector`: the vector with component
  $D^{-1/2}X_{i,p}$ at the pair $(i,p)$.

## Main results

* `ChoiJamiolkowski.nPositiveAmpliation_rankOne_eq_rightCompression`: the
  ampliation of the associated rank-one matrix is exactly that compression.
* `ChoiJamiolkowski.rightTensorMatrix_mul_choiMatrix_mul_conjTranspose`: the
  same compression is the sandwich by the right tensor factor.
* `ChoiJamiolkowski.compressedOmegaVector_hasSchmidtRankLE`: the compressed
  maximally entangled vector has Schmidt rank at most the compression dimension.
* `ChoiJamiolkowski.exists_squareCompression_of_hasSchmidtRankLE`: every
  square bipartite vector of bounded Schmidt rank comes from a square
  right-factor compression with the same rank bound.
* `ChoiJamiolkowski.isNPositiveMap_iff_forall_rightCompression_posSemidef`:
  `k`-positivity is equivalent to positivity of all rectangular right-factor
  Choi compressions.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 3,
  Proposition 3.1, equation (3.4)][Wolf2012QChannels]
-/

open scoped Matrix BigOperators ComplexOrder
open Matrix Finset

namespace ChoiJamiolkowski

variable {D k : ℕ}

/-- The right-factor Choi compression, written in the index convention of the
blockwise ampliation.  Here `X : Matrix (Fin D) (Fin k) ℂ` carries the original
Choi auxiliary index and the `k`-dimensional ampliation index.  The
$(i,p),(j,q)$ entry is
$\sum_{a,b} X_{a,p}\,\tau_{(i,a),(j,b)}\,\overline{X_{b,q}}$, where $\tau$ is
the Choi matrix of `T`. -/
noncomputable def rightCompression
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (X : Matrix (Fin D) (Fin k) ℂ) :
    Matrix (Fin D × Fin k) (Fin D × Fin k) ℂ :=
  Matrix.of fun ip jq =>
    ∑ a : Fin D, ∑ b : Fin D,
      X a ip.2 * choiMatrix T (ip.1, a) (jq.1, b) * star (X b jq.2)

/-- The entry formula for the right-factor compression of the Choi matrix.  The
$(i,p),(j,q)$ entry is
$\sum_{a,b} X_{a,p}\,\tau_{(i,a),(j,b)}\,\overline{X_{b,q}}$, where $\tau$ is
the Choi matrix of `T`. -/
theorem rightCompression_apply
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (X : Matrix (Fin D) (Fin k) ℂ) (i j : Fin D) (p q : Fin k) :
    rightCompression T X (i, p) (j, q) =
      ∑ a : Fin D, ∑ b : Fin D,
        X a p * choiMatrix T (i, a) (j, b) * star (X b q) :=
  rfl

/-- The matrix representing the right tensor factor in the Choi-compression
index convention.  Its entry from the Choi index `(j,a)` to the compressed
index `(i,p)` is $\delta_{ij}X_{a,p}$.  This is the matrix form used in
Wolf, Chapter 3, Proposition 3.1, item 2. -/
noncomputable def rightTensorMatrix (X : Matrix (Fin D) (Fin k) ℂ) :
    Matrix (Fin D × Fin k) (Fin D × Fin D) ℂ :=
  Matrix.of fun ip ja => if ip.1 = ja.1 then X ja.2 ip.2 else 0

/-- Sandwiching the Choi matrix by the right tensor factor gives exactly the
right-factor compression entries.  In Wolf's notation this is the identity
between $(\mathbf{1}\otimes X)\tau(\mathbf{1}\otimes X)^\dagger$ and the
matrix with entries
$\sum_{a,b} X_{a,p}\tau_{(i,a),(j,b)}\overline{X_{b,q}}$. -/
theorem rightTensorMatrix_mul_choiMatrix_mul_conjTranspose
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (X : Matrix (Fin D) (Fin k) ℂ) :
    rightTensorMatrix X * choiMatrix T * (rightTensorMatrix X)ᴴ =
      rightCompression T X := by
  classical
  ext ⟨i, p⟩ ⟨j, q⟩
  simp only [rightTensorMatrix, rightCompression, Matrix.mul_apply, Matrix.of_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single j]
  · rw [Finset.sum_comm]
    simp [Finset.mul_sum, mul_assoc, mul_comm]
  · intro x _ hx
    simp [Ne.symm hx]
  · simp

/-- The coefficient vector obtained from the normalized maximally entangled
vector by applying `X` on the right tensor factor. -/
noncomputable def compressedOmegaVector (X : Matrix (Fin D) (Fin k) ℂ) :
    Fin D × Fin k → ℂ :=
  fun ip => ((1 : ℂ) / ((D : ℝ).sqrt : ℂ)) * X ip.1 ip.2

/-- For `D > 0`, the compressed maximally entangled vector has Schmidt rank
equal to the rank of the right-factor matrix. -/
theorem compressedOmegaVector_schmidtRank_eq_rank [NeZero D]
    (X : Matrix (Fin D) (Fin k) ℂ) :
    Matrix.schmidtRank (compressedOmegaVector X) = X.rank := by
  have hDpos : 0 < (D : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne D)
  have hc : ((1 : ℂ) / ((D : ℝ).sqrt : ℂ)) ≠ 0 := by
    have hsqrt_ne : ((D : ℝ).sqrt : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_ne_zero'.mpr hDpos)
    exact div_ne_zero one_ne_zero hsqrt_ne
  have hcoeff :
      Matrix.schmidtCoeffMatrix (compressedOmegaVector X) =
        ((1 : ℂ) / ((D : ℝ).sqrt : ℂ)) • X := by
    ext i p
    simp [Matrix.schmidtCoeffMatrix, compressedOmegaVector]
  rw [Matrix.schmidtRank, hcoeff]
  exact Matrix.rank_smul_of_ne_zero hc X

/-- The vector obtained by applying a `D × k` matrix on the right tensor factor
of the maximally entangled vector has Schmidt rank at most `k`. -/
theorem compressedOmegaVector_hasSchmidtRankLE
    (X : Matrix (Fin D) (Fin k) ℂ) :
    Matrix.HasSchmidtRankLE k (compressedOmegaVector X) := by
  simpa [Matrix.HasSchmidtRankLE, Matrix.schmidtRank, Matrix.schmidtCoeffMatrix,
    compressedOmegaVector] using
    Matrix.rank_le_card_width (Matrix.schmidtCoeffMatrix (compressedOmegaVector X))

/-- For `D > 0`, every vector in $\mathbb{C}^D\otimes\mathbb{C}^D$ is obtained
from the maximally entangled vector by applying a square right-factor matrix,
and the matrix rank agrees with the Schmidt rank of the vector. -/
theorem exists_squareCompression_of_vector [NeZero D]
    (ψ : Fin D × Fin D → ℂ) :
    ∃ X : Matrix (Fin D) (Fin D) ℂ,
      compressedOmegaVector X = ψ ∧ X.rank = Matrix.schmidtRank ψ := by
  let X : Matrix (Fin D) (Fin D) ℂ :=
    fun a p => (((D : ℝ).sqrt : ℂ)) * ψ (a, p)
  have hDpos : 0 < (D : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne D)
  have hsqrt_ne : ((D : ℝ).sqrt : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr hDpos)
  have hvec : compressedOmegaVector X = ψ := by
    ext ip
    rcases ip with ⟨i, p⟩
    simp only [compressedOmegaVector, X]
    field_simp [hsqrt_ne]
  refine ⟨X, hvec, ?_⟩
  simpa [hvec] using (compressedOmegaVector_schmidtRank_eq_rank (X := X)).symm

/-- For `D > 0`, a square bipartite vector with Schmidt rank at most `r` has a
square right-factor matrix representative of rank at most `r`. -/
theorem exists_squareCompression_of_hasSchmidtRankLE [NeZero D]
    {r : ℕ} {ψ : Fin D × Fin D → ℂ} (hψ : Matrix.HasSchmidtRankLE r ψ) :
    ∃ X : Matrix (Fin D) (Fin D) ℂ,
      compressedOmegaVector X = ψ ∧ X.rank ≤ r := by
  obtain ⟨X, hXvec, hXrank⟩ := exists_squareCompression_of_vector (D := D) ψ
  exact ⟨X, hXvec, hXrank.trans_le hψ⟩

/-- For the vector `compressedOmegaVector X`, the `k`-fold ampliation of the
rank-one matrix $|\psi\rangle\langle\psi|$ by `T` is the right-factor Choi
compression by `X`. -/
theorem nPositiveAmpliation_rankOne_eq_rightCompression
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (X : Matrix (Fin D) (Fin k) ℂ) :
    nPositiveAmpliation k T
        (Matrix.vecMulVec (compressedOmegaVector X) (star (compressedOmegaVector X))) =
      rightCompression T X := by
  classical
  ext ⟨i, p⟩ ⟨j, q⟩
  let c : ℂ := (1 : ℂ) / ((D : ℝ).sqrt : ℂ)
  have hblock :
      (Matrix.of fun a b =>
          Matrix.vecMulVec (compressedOmegaVector X) (star (compressedOmegaVector X))
            (a, p) (b, q)) =
        ∑ a : Fin D, ∑ b : Fin D,
          (X a p * star (X b q)) • Matrix.bipartiteSlice (Matrix.omegaProj D) a b := by
    calc
      (Matrix.of fun a b =>
          Matrix.vecMulVec (compressedOmegaVector X) (star (compressedOmegaVector X))
            (a, p) (b, q))
          = Matrix.of fun a b => (X a p * star (X b q)) * (c * star c) := by
            ext a b
            simp [compressedOmegaVector, c, Matrix.vecMulVec_apply]
            ring
      _ = ∑ a : Fin D, ∑ b : Fin D,
          (X a p * star (X b q)) • Matrix.bipartiteSlice (Matrix.omegaProj D) a b := by
            rw [Matrix.matrix_eq_sum_single
              (Matrix.of fun a b => (X a p * star (X b q)) * (c * star c))]
            simp [ChoiJamiolkowski.omegaSlice_eq_single, c, Matrix.smul_single,
              smul_eq_mul]
  calc
    nPositiveAmpliation k T
        (Matrix.vecMulVec (compressedOmegaVector X) (star (compressedOmegaVector X)))
        (i, p) (j, q)
        = T (Matrix.of fun a b =>
            Matrix.vecMulVec (compressedOmegaVector X) (star (compressedOmegaVector X))
              (a, p) (b, q)) i j := rfl
    _ = T (∑ a : Fin D, ∑ b : Fin D,
          (X a p * star (X b q)) • Matrix.bipartiteSlice (Matrix.omegaProj D) a b) i j := by
        rw [hblock]
    _ = (∑ a : Fin D, ∑ b : Fin D,
          (X a p * star (X b q)) • T (Matrix.bipartiteSlice (Matrix.omegaProj D) a b)) i j := by
        simp [map_sum]
    _ = rightCompression T X (i, p) (j, q) := by
        rw [rightCompression_apply]
        simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, choiMatrix_apply]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        ring_nf

/-- Rectangular compression form of Wolf, Proposition 3.1, equation (3.4), for
endomorphisms of matrix algebras: when `D > 0`, `k`-positivity is equivalent to
positivity of every right-factor compression of the Choi matrix by a matrix in
`M_{D,k}`. -/
theorem isNPositiveMap_iff_forall_rightCompression_posSemidef [NeZero D]
    (k : ℕ) (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    IsNPositiveMap k T ↔
      ∀ X : Matrix (Fin D) (Fin k) ℂ, (rightCompression T X).PosSemidef := by
  constructor
  · intro hT X
    rw [← nPositiveAmpliation_rankOne_eq_rightCompression (T := T) (X := X)]
    exact (isNPositiveMap_iff_forall_ampliation_rank_one_posSemidef k T).mp hT
      (compressedOmegaVector X)
  · intro hX
    rw [isNPositiveMap_iff_forall_ampliation_rank_one_posSemidef]
    intro φ
    let X : Matrix (Fin D) (Fin k) ℂ :=
      fun a p => (((D : ℝ).sqrt : ℂ)) * φ (a, p)
    have hvec : compressedOmegaVector X = φ := by
      have hDpos : 0 < (D : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne D)
      have hsqrt_ne : ((D : ℝ).sqrt : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_ne_zero'.mpr hDpos)
      ext ip
      rcases ip with ⟨i, p⟩
      simp only [compressedOmegaVector, X]
      field_simp [hsqrt_ne]
    rw [← hvec]
    rw [nPositiveAmpliation_rankOne_eq_rightCompression]
    exact hX X

/-- A `k`-positive map has positive Choi sandwiches by every right tensor
factor `X : M_{D,k}(\mathbb{C})`.  This is the forward implication of the
projection-compression formulation before requiring that `X` comes from a
rank-`k` Hermitian projection. -/
theorem IsNPositiveMap.rightTensor_choiMatrix_sandwich_posSemidef [NeZero D]
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsNPositiveMap k T) (X : Matrix (Fin D) (Fin k) ℂ) :
    (rightTensorMatrix X * choiMatrix T * (rightTensorMatrix X)ᴴ).PosSemidef := by
  rw [rightTensorMatrix_mul_choiMatrix_mul_conjTranspose]
  exact (isNPositiveMap_iff_forall_rightCompression_posSemidef k T).mp hT X

end ChoiJamiolkowski

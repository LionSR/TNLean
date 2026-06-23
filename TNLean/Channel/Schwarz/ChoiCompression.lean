/-
Copyright (c) 2026 Sirui Lu and TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Channel.SchmidtRank
import TNLean.Channel.Schwarz.TwoPositive
import Mathlib.Analysis.InnerProductSpace.Positive

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
* `ChoiJamiolkowski.compressedOmegaVector_schmidtRank_eq_rank`: the compressed
  maximally entangled vector has Schmidt rank equal to the rank of the
  right-factor matrix.
* `ChoiJamiolkowski.hasSchmidtRankLE_iff_exists_rank_le_compressedOmegaVector`:
  Wolf's square-matrix parametrization of vectors of bounded Schmidt rank.
* `ChoiJamiolkowski.isNPositiveMap_iff_forall_rightCompression_posSemidef`:
  `k`-positivity is equivalent to positivity of all rectangular right-factor
  Choi compressions.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 3,
  Proposition 3.1, equation (3.4)][Wolf2012QChannels]
-/

open scoped Matrix BigOperators ComplexOrder
open Matrix Finset

namespace Matrix

/-- Over a finite complex coordinate space, nonnegativity of all matrix
quadratic forms already implies positive semidefiniteness.  The Hermitian part
is recovered by the complex polarization identity. -/
theorem posSemidef_of_dotProduct_mulVec_nonneg_complex
    {n : Type*} [Fintype n] {M : Matrix n n ℂ}
    (hM : ∀ x : n → ℂ, (0 : ℂ) ≤ star x ⬝ᵥ (M *ᵥ x)) : M.PosSemidef := by
  classical
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ hM
  rw [← Matrix.isSymmetric_toEuclideanLin_iff]
  have hpos : (Matrix.toEuclideanLin M).IsPositive := by
    rw [LinearMap.isPositive_iff_complex]
    intro x
    have hx_nonneg : (0 : ℂ) ≤ star x.ofLp ⬝ᵥ (M *ᵥ x.ofLp) := hM x.ofLp
    have hx_real :
        star (star x.ofLp ⬝ᵥ (M *ᵥ x.ofLp)) =
          star x.ofLp ⬝ᵥ (M *ᵥ x.ofLp) := by
      rw [RCLike.star_def]
      exact RCLike.conj_eq_iff_im.mpr (RCLike.nonneg_iff.mp hx_nonneg).2
    have hinner :
        inner ℂ ((Matrix.toEuclideanLin M) x) x =
          star (star x.ofLp ⬝ᵥ (M *ᵥ x.ofLp)) := by
      change inner ℂ (((Matrix.toLpLin 2 2) M) x) x =
        star (star x.ofLp ⬝ᵥ (M *ᵥ x.ofLp))
      rw [Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct]
      rw [dotProduct_comm]
      simp [dotProduct, mul_comm]
    constructor
    · rw [hinner, hx_real]
      exact RCLike.conj_eq_iff_re.mp (by simpa [RCLike.star_def] using hx_real)
    · rw [hinner, hx_real]
      exact (RCLike.nonneg_iff.mp hx_nonneg).1
  exact hpos.isSymmetric

end Matrix

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

/-- The quadratic form of the Choi sandwich by the right tensor factor is the
Choi quadratic form evaluated on the pulled-back vector. -/
theorem rightTensor_choiMatrix_quadraticForm_eq
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (X : Matrix (Fin D) (Fin k) ℂ) (η : Fin D × Fin k → ℂ) :
    star η ⬝ᵥ
        ((rightTensorMatrix X * choiMatrix T * (rightTensorMatrix X)ᴴ) *ᵥ η) =
      star ((rightTensorMatrix X)ᴴ *ᵥ η) ⬝ᵥ
        (choiMatrix T *ᵥ ((rightTensorMatrix X)ᴴ *ᵥ η)) := by
  have hmul :
      ((rightTensorMatrix X * choiMatrix T * (rightTensorMatrix X)ᴴ) *ᵥ η) =
        rightTensorMatrix X *ᵥ
          (choiMatrix T *ᵥ ((rightTensorMatrix X)ᴴ *ᵥ η)) := by
    simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hstar :
      star ((rightTensorMatrix X)ᴴ *ᵥ η) = star η ᵥ* rightTensorMatrix X := by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
  rw [hmul, Matrix.dotProduct_mulVec, ← hstar]

/-- The quadratic form of the right-factor compression is the Choi quadratic
form evaluated on the vector pulled back by the adjoint right tensor factor. -/
theorem rightCompression_quadraticForm_eq_choiMatrix_quadraticForm
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (X : Matrix (Fin D) (Fin k) ℂ) (η : Fin D × Fin k → ℂ) :
    star η ⬝ᵥ (rightCompression T X *ᵥ η) =
      star ((rightTensorMatrix X)ᴴ *ᵥ η) ⬝ᵥ
        (choiMatrix T *ᵥ ((rightTensorMatrix X)ᴴ *ᵥ η)) := by
  rw [← rightTensorMatrix_mul_choiMatrix_mul_conjTranspose (T := T) (X := X)]
  exact rightTensor_choiMatrix_quadraticForm_eq T X η

/-- The coefficient matrix of the vector pulled back by the adjoint right
tensor factor is the product of the coefficient matrix of the compressed vector
with the adjoint of the right-factor matrix. -/
theorem schmidtCoeffMatrix_rightTensorMatrix_conjTranspose_mulVec
    (X : Matrix (Fin D) (Fin k) ℂ) (η : Fin D × Fin k → ℂ) :
    Matrix.schmidtCoeffMatrix ((rightTensorMatrix X)ᴴ *ᵥ η) =
      Matrix.schmidtCoeffMatrix η * Xᴴ := by
  classical
  ext j a
  simp only [Matrix.schmidtCoeffMatrix, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    rightTensorMatrix, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single j]
  · simp [mul_comm]
  · intro i _ hij
    simp [hij]
  · simp

/-- Pulling a vector back by the adjoint right tensor factor gives a vector of
Schmidt rank at most the compression dimension. -/
theorem rightTensorMatrix_conjTranspose_mulVec_hasSchmidtRankLE
    (X : Matrix (Fin D) (Fin k) ℂ) (η : Fin D × Fin k → ℂ) :
    Matrix.HasSchmidtRankLE k ((rightTensorMatrix X)ᴴ *ᵥ η) := by
  have hrank : (Matrix.schmidtCoeffMatrix ((rightTensorMatrix X)ᴴ *ᵥ η)).rank ≤ k := by
    rw [schmidtCoeffMatrix_rightTensorMatrix_conjTranspose_mulVec]
    calc
      (Matrix.schmidtCoeffMatrix η * Xᴴ).rank ≤ (Xᴴ).rank :=
        Matrix.rank_mul_le_right (Matrix.schmidtCoeffMatrix η) Xᴴ
      _ = X.rank := Matrix.rank_conjTranspose X
      _ ≤ Fintype.card (Fin k) := Matrix.rank_le_card_width X
      _ = k := by simp
  simpa [Matrix.HasSchmidtRankLE, Matrix.schmidtRank] using hrank

/-- Every vector of Schmidt rank at most `k` is obtained by pulling back a
vector in the `D × k` compressed space through the adjoint of a right tensor
factor. -/
theorem exists_rightTensorMatrix_conjTranspose_mulVec_of_hasSchmidtRankLE
    {ψ : Fin D × Fin D → ℂ} (hψ : Matrix.HasSchmidtRankLE k ψ) :
    ∃ X : Matrix (Fin D) (Fin k) ℂ, ∃ η : Fin D × Fin k → ℂ,
      (rightTensorMatrix X)ᴴ *ᵥ η = ψ := by
  classical
  let A : Matrix (Fin D) (Fin D) ℂ := Matrix.schmidtCoeffMatrix ψ
  have hA : A.rank ≤ k := by
    simpa [A, Matrix.HasSchmidtRankLE, Matrix.schmidtRank] using hψ
  obtain ⟨B, C, hBC⟩ := Matrix.exists_mul_eq_of_rank_le A hA
  let X : Matrix (Fin D) (Fin k) ℂ := Cᴴ
  let η : Fin D × Fin k → ℂ := fun ip => B ip.1 ip.2
  refine ⟨X, η, ?_⟩
  ext ip
  rcases ip with ⟨j, a⟩
  calc
    ((rightTensorMatrix X)ᴴ *ᵥ η) (j, a)
        = Matrix.schmidtCoeffMatrix ((rightTensorMatrix X)ᴴ *ᵥ η) j a := rfl
    _ = (B * C) j a := by
        rw [schmidtCoeffMatrix_rightTensorMatrix_conjTranspose_mulVec]
        have hηcoeff : Matrix.schmidtCoeffMatrix η = B := by
          ext i p
          rfl
        rw [hηcoeff]
        simp only [X, Matrix.conjTranspose_conjTranspose]
    _ = A j a := by rw [hBC]
    _ = ψ (j, a) := rfl

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
  let c : ℂ := (1 : ℂ) / ((D : ℝ).sqrt : ℂ)
  have hDpos : 0 < (D : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne D)
  have hsqrt_ne : ((D : ℝ).sqrt : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr hDpos)
  have hc_ne : c ≠ 0 := by
    simp [c, hsqrt_ne]
  have hcoeff :
      Matrix.schmidtCoeffMatrix (compressedOmegaVector X) = c • X := by
    ext i p
    simp [Matrix.schmidtCoeffMatrix, compressedOmegaVector, c]
  rw [Matrix.schmidtRank, hcoeff]
  exact Matrix.rank_smul_of_ne_zero hc_ne X

/-- The vector obtained by applying a `D × k` matrix on the right tensor factor
of the maximally entangled vector has Schmidt rank at most `k`. -/
theorem compressedOmegaVector_hasSchmidtRankLE
    (X : Matrix (Fin D) (Fin k) ℂ) :
    Matrix.HasSchmidtRankLE k (compressedOmegaVector X) := by
  simpa [Matrix.HasSchmidtRankLE, Matrix.schmidtRank, Matrix.schmidtCoeffMatrix,
    compressedOmegaVector] using
    Matrix.rank_le_card_width (Matrix.schmidtCoeffMatrix (compressedOmegaVector X))

/-- If the square compression matrix has rank at most k, then the associated
compressed maximally entangled vector has Schmidt rank at most k. -/
theorem compressedOmegaVector_hasSchmidtRankLE_of_rank_le [NeZero D]
    {X : Matrix (Fin D) (Fin D) ℂ} {k : ℕ} (hX : X.rank ≤ k) :
    Matrix.HasSchmidtRankLE k (compressedOmegaVector X) := by
  simpa [Matrix.HasSchmidtRankLE, compressedOmegaVector_schmidtRank_eq_rank] using hX

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

/-- Wolf's square-matrix parametrization of bounded Schmidt-rank vectors.
When D is positive, a vector in $\mathbb{C}^D \otimes \mathbb{C}^D$ has Schmidt
rank at most k if and only if it is obtained from the normalized maximally
entangled vector by applying a square matrix of rank at most k on the right
tensor factor. -/
theorem hasSchmidtRankLE_iff_exists_rank_le_compressedOmegaVector [NeZero D]
    {k : ℕ} {ψ : Fin D × Fin D → ℂ} :
    Matrix.HasSchmidtRankLE k ψ ↔
      ∃ X : Matrix (Fin D) (Fin D) ℂ, X.rank ≤ k ∧ compressedOmegaVector X = ψ := by
  constructor
  · intro hψ
    obtain ⟨X, hXvec, hXrank⟩ := exists_squareCompression_of_hasSchmidtRankLE
      (D := D) hψ
    exact ⟨X, hXrank, hXvec⟩
  · rintro ⟨X, hX, rfl⟩
    exact compressedOmegaVector_hasSchmidtRankLE_of_rank_le hX

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

/-- Converse Schmidt-rank test for Wolf's Choi criterion.  If all
Schmidt-rank-`≤ k` vectors have nonnegative Choi quadratic form, then the map
is `k`-positive. -/
theorem isNPositiveMap_of_forall_hasSchmidtRankLE_choiMatrix_quadraticForm_nonneg [NeZero D]
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hψ : ∀ ψ : Fin D × Fin D → ℂ, Matrix.HasSchmidtRankLE k ψ →
      (0 : ℂ) ≤ star ψ ⬝ᵥ (choiMatrix T *ᵥ ψ)) :
    IsNPositiveMap k T := by
  rw [isNPositiveMap_iff_forall_rightCompression_posSemidef]
  intro X
  refine Matrix.posSemidef_of_dotProduct_mulVec_nonneg_complex ?_
  intro η
  rw [rightCompression_quadraticForm_eq_choiMatrix_quadraticForm (T := T) (X := X) (η := η)]
  exact hψ _ (rightTensorMatrix_conjTranspose_mulVec_hasSchmidtRankLE X η)

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

/-- Forward direction of Wolf's Schmidt-rank expectation criterion.  If `T` is
`k`-positive, then the Choi quadratic form is nonnegative on every vector of
Schmidt rank at most `k`. -/
theorem IsNPositiveMap.choiMatrix_quadraticForm_nonneg_of_hasSchmidtRankLE [NeZero D]
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsNPositiveMap k T) {ψ : Fin D × Fin D → ℂ}
    (hψ : Matrix.HasSchmidtRankLE k ψ) :
    0 ≤ star ψ ⬝ᵥ (choiMatrix T *ᵥ ψ) := by
  obtain ⟨X, η, hη⟩ :=
    exists_rightTensorMatrix_conjTranspose_mulVec_of_hasSchmidtRankLE (D := D) hψ
  have hcomp : (rightCompression T X).PosSemidef :=
    (isNPositiveMap_iff_forall_rightCompression_posSemidef k T).mp hT X
  have hq := hcomp.dotProduct_mulVec_nonneg η
  rw [rightCompression_quadraticForm_eq_choiMatrix_quadraticForm] at hq
  simpa [hη] using hq

/-- Schmidt-rank expectation criterion for Wolf's Choi matrix:
`k`-positivity is equivalent to nonnegativity of the Choi quadratic form on all
vectors of Schmidt rank at most `k`. -/
theorem isNPositiveMap_iff_forall_hasSchmidtRankLE_choiMatrix_quadraticForm_nonneg
    [NeZero D]
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ} :
    IsNPositiveMap k T ↔
      ∀ ψ : Fin D × Fin D → ℂ, Matrix.HasSchmidtRankLE k ψ →
        (0 : ℂ) ≤ star ψ ⬝ᵥ (choiMatrix T *ᵥ ψ) := by
  constructor
  · intro hT ψ hψ
    exact IsNPositiveMap.choiMatrix_quadraticForm_nonneg_of_hasSchmidtRankLE hT hψ
  · intro hψ
    exact isNPositiveMap_of_forall_hasSchmidtRankLE_choiMatrix_quadraticForm_nonneg hψ

end ChoiJamiolkowski

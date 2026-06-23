/-
Copyright (c) 2026 Sirui Lu and TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Channel.SchmidtRank
import TNLean.Channel.Schwarz.PositiveOnAbelian.Basic
import TNLean.Channel.Schwarz.TwoPositive
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

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
* `ChoiJamiolkowski.rightTensorMatrix_mul_rightTensorMatrix`: right tensor
  factors multiply by multiplying the corresponding right-factor matrices.
* Fixed-column compression lemma:
  a square right-factor sandwich controls each rectangular compression whose
  columns it fixes; see
  `rightCompression_posSemidef_of_rightTensorMatrix_sandwich_posSemidef_of_mul_eq_self`.
* `Matrix.exists_mul_conjTranspose_of_isHermitian_idempotent_rank`: a Hermitian
  idempotent matrix of rank `k` factors as `P = V * Vᴴ`.
* `Matrix.exists_isHermitian_idempotent_rank_mul_eq_self`: every rectangular
  right factor with `k ≤ D` is fixed by some Hermitian idempotent rank-`k`
  projection.
* `IsNPositiveMap.rightTensor_choiMatrix_sandwich_posSemidef_of_isHermitian_idempotent_rank`:
  `k`-positivity implies positivity of the Choi sandwich compressed by a
  Hermitian idempotent of rank `k`.
* `isNPositiveMap_iff_forall_rankProjection_rightTensor_choiMatrix_sandwich_posSemidef`:
  Wolf's rank-`k` projection form of the Choi criterion.

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

namespace Submodule

/-- In a finite-dimensional vector space, any subspace of dimension at most `r`
is contained in a subspace of dimension exactly `r`, provided `r` is no larger
than the ambient dimension. -/
theorem exists_le_finrank_eq {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] (W : Submodule K V) {r : ℕ}
    (hW : Module.finrank K W ≤ r) (hr : r ≤ Module.finrank K V) :
    ∃ U : Submodule K V, W ≤ U ∧ Module.finrank K U = r := by
  classical
  let P : ℕ → Prop := fun n => ∀ W : Submodule K V,
    r - Module.finrank K W = n → Module.finrank K W ≤ r →
      ∃ U : Submodule K V, W ≤ U ∧ Module.finrank K U = r
  have hP : ∀ n, P n := by
    intro n
    induction n with
    | zero =>
        intro W hdiff hWle
        refine ⟨W, le_rfl, ?_⟩
        omega
    | succ n ih =>
        intro W hdiff hWle
        have hlt : Module.finrank K W < r := by omega
        have hWV : Module.finrank K W < Module.finrank K V := lt_of_lt_of_le hlt hr
        obtain ⟨v, hv⟩ := Submodule.exists_of_finrank_lt W hWV
        let W' : Submodule K V := W ⊔ Submodule.span K ({v} : Set V)
        have hWleW' : W ≤ W' := le_sup_left
        have hvnot : v ∉ W := by
          intro hvW
          exact hv 1 one_ne_zero (by simpa using hvW)
        have hfinW' : Module.finrank K W' = Module.finrank K W + 1 := by
          simpa [W'] using
            (Submodule.finrank_sup_span_singleton (K := K) (V := V) (p := W) hvnot)
        have hW'le : Module.finrank K W' ≤ r := by omega
        have hdiff' : r - Module.finrank K W' = n := by omega
        obtain ⟨U, hW'U, hUfin⟩ := ih W' hdiff' hW'le
        exact ⟨U, hWleW'.trans hW'U, hUfin⟩
  exact hP (r - Module.finrank K W) W rfl hW

end Submodule

namespace Matrix

/-- Every finite-dimensional Hermitian idempotent matrix of rank `k` has a
factorization `P = V * Vᴴ` with `k` columns.  The proof identifies `P` with the
orthogonal projection onto its range, chooses an orthonormal basis of that range,
and takes the basis vectors as the columns of `V`.

This is the finite-dimensional projection factorization used in Wolf,
Proposition 3.1, item 2. -/
theorem exists_mul_conjTranspose_of_isHermitian_idempotent_rank
    {D k : ℕ} (P : Matrix (Fin D) (Fin D) ℂ)
    (hP : P.IsHermitian) (hP_idem : P * P = P) (hrank : P.rank = k) :
    ∃ V : Matrix (Fin D) (Fin k) ℂ, P = V * Vᴴ := by
  let E := EuclideanSpace ℂ (Fin D)
  let p : E →ₗ[ℂ] E := Matrix.toEuclideanLin P
  have hp : p.IsSymmetricProjection := by
    constructor
    · change Matrix.toEuclideanLin P * Matrix.toEuclideanLin P = Matrix.toEuclideanLin P
      rw [PositiveOnAbelian.Internal.toEuclideanLin_mul, hP_idem]
    · exact (Matrix.isSymmetric_toEuclideanLin_iff (A := P)).mpr hP
  obtain ⟨horth, hp_eq⟩ :=
    LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.mp hp
  letI : (LinearMap.range p).HasOrthogonalProjection := horth
  have hrange : Module.finrank ℂ (LinearMap.range p) = k := by
    have hrank_range0 :
        P.rank = Module.finrank ℂ (LinearMap.range
          (Matrix.toEuclideanLin P : E →ₗ[ℂ] E)) := by
      rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
      exact Matrix.rank_eq_finrank_range_toLin P
        (EuclideanSpace.basisFun (Fin D) ℂ).toBasis
        (EuclideanSpace.basisFun (Fin D) ℂ).toBasis
    have hrank_range : P.rank = Module.finrank ℂ (LinearMap.range p) := by
      simpa [p, E] using hrank_range0
    exact hrank_range.symm.trans hrank
  let b0 : OrthonormalBasis (Fin (Module.finrank ℂ (LinearMap.range p))) ℂ
      (LinearMap.range p) :=
    stdOrthonormalBasis ℂ (LinearMap.range p)
  let b : OrthonormalBasis (Fin k) ℂ (LinearMap.range p) :=
    b0.reindex (finCongr hrange)
  let V : Matrix (Fin D) (Fin k) ℂ := fun a j => (b j : E) a
  refine ⟨V, ?_⟩
  apply Matrix.toEuclideanLin.injective
  have hVV : V * Vᴴ = ∑ j : Fin k, Matrix.vecMulVec (b j : E) (star (b j : E)) := by
    dsimp [V]
    ext a c
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.vecMulVec]
  have hsum_rankOne :
      Matrix.toEuclideanLin (V * Vᴴ) =
        ∑ j : Fin k, (InnerProductSpace.rankOne ℂ (b j : E) (b j : E) : E →ₗ[ℂ] E) := by
    rw [hVV]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    have h := congrArg Matrix.toEuclideanLin
      (InnerProductSpace.symm_toEuclideanLin_rankOne (𝕜 := ℂ)
        (x := (b j : E)) (y := (b j : E)))
    simpa using h.symm
  have hstar_linear :
      ((LinearMap.range p).starProjection : E →ₗ[ℂ] E) =
        ∑ j : Fin k, (InnerProductSpace.rankOne ℂ (b j : E) (b j : E) : E →ₗ[ℂ] E) := by
    have hstar := OrthonormalBasis.starProjection_eq_sum_rankOne (U := LinearMap.range p) b
    simpa [ContinuousLinearMap.toLinearMap_sum] using
      congrArg (fun L : E →L[ℂ] E => (L : E →ₗ[ℂ] E)) hstar
  calc
    Matrix.toEuclideanLin P = p := rfl
    _ = ((LinearMap.range p).starProjection : E →ₗ[ℂ] E) := hp_eq
    _ = ∑ j : Fin k, (InnerProductSpace.rankOne ℂ (b j : E) (b j : E) : E →ₗ[ℂ] E) :=
      hstar_linear
    _ = Matrix.toEuclideanLin (V * Vᴴ) := hsum_rankOne.symm

/-- The linear map represented by a rectangular product is the composition of
the two represented linear maps. -/
lemma toEuclideanLin_mul_rect {D k : ℕ}
    (P : Matrix (Fin D) (Fin D) ℂ) (X : Matrix (Fin D) (Fin k) ℂ) :
    Matrix.toEuclideanLin (P * X) =
      (Matrix.toEuclideanLin P).comp (Matrix.toEuclideanLin X) := by
  change Matrix.toLin (EuclideanSpace.basisFun (Fin k) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin D) ℂ).toBasis (P * X) =
    (Matrix.toLin (EuclideanSpace.basisFun (Fin D) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin D) ℂ).toBasis P).comp
      (Matrix.toLin (EuclideanSpace.basisFun (Fin k) ℂ).toBasis
        (EuclideanSpace.basisFun (Fin D) ℂ).toBasis X)
  exact Matrix.toLin_mul (EuclideanSpace.basisFun (Fin k) ℂ).toBasis
    (EuclideanSpace.basisFun (Fin D) ℂ).toBasis
    (EuclideanSpace.basisFun (Fin D) ℂ).toBasis P X

/-- If `k ≤ D`, then every rectangular matrix `X : M_{D,k}(ℂ)` is fixed by
some rank-`k` Hermitian idempotent on the left.  The projection is the
orthogonal projection onto a `k`-dimensional subspace containing the column
space of `X`.

This is the geometric converse step in Wolf, Proposition 3.1, item 2. -/
theorem exists_isHermitian_idempotent_rank_mul_eq_self
    {D k : ℕ} (hkD : k ≤ D) (X : Matrix (Fin D) (Fin k) ℂ) :
    ∃ P : Matrix (Fin D) (Fin D) ℂ,
      P.IsHermitian ∧ P * P = P ∧ P.rank = k ∧ P * X = X := by
  classical
  let W : Submodule ℂ (EuclideanSpace ℂ (Fin D)) :=
    LinearMap.range (Matrix.toEuclideanLin X : EuclideanSpace ℂ (Fin k) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin D))
  have hWfin : Module.finrank ℂ W ≤ k := by
    have hrank_range0 : X.rank = Module.finrank ℂ W := by
      change X.rank = Module.finrank ℂ (LinearMap.range
        ((Matrix.toLin (EuclideanSpace.basisFun (Fin k) ℂ).toBasis
          (EuclideanSpace.basisFun (Fin D) ℂ).toBasis) X))
      exact Matrix.rank_eq_finrank_range_toLin X
        (EuclideanSpace.basisFun (Fin D) ℂ).toBasis
        (EuclideanSpace.basisFun (Fin k) ℂ).toBasis
    rw [← hrank_range0]
    exact Matrix.rank_le_width X
  have hkE : k ≤ Module.finrank ℂ (EuclideanSpace ℂ (Fin D)) := by
    simpa using hkD
  obtain ⟨U, hWU, hUfin⟩ := Submodule.exists_le_finrank_eq W hWfin hkE
  letI : U.HasOrthogonalProjection := inferInstance
  let p : EuclideanSpace ℂ (Fin D) →ₗ[ℂ] EuclideanSpace ℂ (Fin D) :=
    (U.starProjection : EuclideanSpace ℂ (Fin D) →ₗ[ℂ] EuclideanSpace ℂ (Fin D))
  let P : Matrix (Fin D) (Fin D) ℂ := Matrix.toEuclideanLin.symm p
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · exact (Matrix.isSymmetric_toEuclideanLin_iff (A := P)).mp
      (by simpa [P, p] using U.starProjection_isSymmetric)
  · apply Matrix.toEuclideanLin.injective
    rw [toEuclideanLin_mul_rect]
    have hp : p.IsSymmetricProjection := by
      dsimp [p]
      exact Submodule.isSymmetricProjection_starProjection U
    simpa [P, p, Module.End.mul_eq_comp] using hp.isIdempotentElem.eq
  · have hrank_range0 :
        P.rank = Module.finrank ℂ
          (LinearMap.range (Matrix.toEuclideanLin P : EuclideanSpace ℂ (Fin D) →ₗ[ℂ]
            EuclideanSpace ℂ (Fin D))) := by
      change P.rank = Module.finrank ℂ (LinearMap.range
        ((Matrix.toLin (EuclideanSpace.basisFun (Fin D) ℂ).toBasis
          (EuclideanSpace.basisFun (Fin D) ℂ).toBasis) P))
      exact Matrix.rank_eq_finrank_range_toLin P
        (EuclideanSpace.basisFun (Fin D) ℂ).toBasis
        (EuclideanSpace.basisFun (Fin D) ℂ).toBasis
    have hrange :
        LinearMap.range (Matrix.toEuclideanLin P : EuclideanSpace ℂ (Fin D) →ₗ[ℂ]
          EuclideanSpace ℂ (Fin D)) = U := by
      calc
        LinearMap.range (Matrix.toEuclideanLin P : EuclideanSpace ℂ (Fin D) →ₗ[ℂ]
            EuclideanSpace ℂ (Fin D))
            = LinearMap.range p := by simp [P]
        _ = U := by simp [p, Submodule.range_starProjection U]
    rw [hrank_range0, hrange, hUfin]
  · apply Matrix.toEuclideanLin.injective
    rw [toEuclideanLin_mul_rect]
    ext v
    have hvW : Matrix.toEuclideanLin X v ∈ W := by
      exact ⟨v, rfl⟩
    have hvU : Matrix.toEuclideanLin X v ∈ U := hWU hvW
    simp [P, p, Submodule.starProjection_eq_self_iff.mpr hvU]

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

/-- The right-tensor matrix for `X * Xᴴ` factors as `R_Xᴴ * R_X` in the
index convention used for Choi compression. -/
theorem rightTensorMatrix_mul_conjTranspose_eq_conjTranspose_mul_self
    (X : Matrix (Fin D) (Fin k) ℂ) :
    rightTensorMatrix (X * Xᴴ) = (rightTensorMatrix X)ᴴ * rightTensorMatrix X := by
  classical
  ext ⟨i, a⟩ ⟨j, b⟩
  by_cases hij : i = j
  · subst j
    simp only [rightTensorMatrix, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      if_true]
    rw [Fintype.sum_prod_type]
    simp [mul_comm]
  · simp only [rightTensorMatrix, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [Fintype.sum_prod_type]
    have hji : ¬j = i := fun hji => hij hji.symm
    simp [hij, hji]

/-- Multiplication by a square right tensor factor corresponds to multiplication
of the underlying right-factor matrices. -/
theorem rightTensorMatrix_mul_rightTensorMatrix
    (X : Matrix (Fin D) (Fin k) ℂ) (P : Matrix (Fin D) (Fin D) ℂ) :
    rightTensorMatrix X * rightTensorMatrix P = rightTensorMatrix (P * X) := by
  classical
  ext ⟨i, p⟩ ⟨j, a⟩
  simp only [rightTensorMatrix, Matrix.of_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  by_cases hij : i = j
  · subst j
    simp [mul_comm]
  · simp [hij]

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

/-- If a right-factor matrix `P` is presented as `V * Vᴴ`, then its Choi
sandwich is a compression of the rectangular Choi sandwich for `V`. -/
theorem rightTensorMatrix_mul_conjTranspose_choi_sandwich_eq
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (V : Matrix (Fin D) (Fin k) ℂ) :
    rightTensorMatrix (V * Vᴴ) * choiMatrix T * (rightTensorMatrix (V * Vᴴ))ᴴ =
      (rightTensorMatrix V)ᴴ *
        (rightTensorMatrix V * choiMatrix T * (rightTensorMatrix V)ᴴ) *
          rightTensorMatrix V := by
  rw [rightTensorMatrix_mul_conjTranspose_eq_conjTranspose_mul_self]
  simp [Matrix.mul_assoc]

/-- If a right-factor matrix has the form `V * Vᴴ`, then the corresponding
Choi sandwich is positive semidefinite. To recover the full statement of Wolf,
Proposition 3.1, item 2, for an arbitrary rank-`k` orthogonal projection `P`,
one additionally needs a factorization `P = V * Vᴴ`. -/
theorem IsNPositiveMap.rightTensor_choiMatrix_sandwich_posSemidef_of_mul_conjTranspose
    [NeZero D]
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsNPositiveMap k T) (V : Matrix (Fin D) (Fin k) ℂ) :
    (rightTensorMatrix (V * Vᴴ) * choiMatrix T *
      (rightTensorMatrix (V * Vᴴ))ᴴ).PosSemidef := by
  rw [rightTensorMatrix_mul_conjTranspose_choi_sandwich_eq]
  exact
    (IsNPositiveMap.rightTensor_choiMatrix_sandwich_posSemidef hT V).conjTranspose_mul_mul_same
      (rightTensorMatrix V)

/-- Forward projection-compression consequence in Wolf, Proposition 3.1,
item 2.  If `P = Pᴴ`, `P * P = P`, and `rank(P) = k`, then the right-factor
Choi sandwich by `P` is positive semidefinite under `k`-positivity. -/
theorem IsNPositiveMap.rightTensor_choiMatrix_sandwich_posSemidef_of_isHermitian_idempotent_rank
    [NeZero D]
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsNPositiveMap k T) {P : Matrix (Fin D) (Fin D) ℂ}
    (hP : P.IsHermitian) (hP_idem : P * P = P) (hrank : P.rank = k) :
    (rightTensorMatrix P * choiMatrix T * (rightTensorMatrix P)ᴴ).PosSemidef := by
  obtain ⟨V, rfl⟩ :=
    Matrix.exists_mul_conjTranspose_of_isHermitian_idempotent_rank P hP hP_idem hrank
  exact IsNPositiveMap.rightTensor_choiMatrix_sandwich_posSemidef_of_mul_conjTranspose hT V

/-- If a square right factor `P` fixes the columns of `X`, then
positivity of the Choi sandwich by `P` implies positivity of the rectangular
right compression by `X`.  This is the algebraic half of the converse direction
in Wolf, Proposition 3.1, item 2; the remaining geometric step is to choose a
rank-`k` projection `P` with `P * X = X`.

Source: Wolf, Chapter 3, Proposition 3.1 proof, lines 110--111. -/
theorem rightCompression_posSemidef_of_rightTensorMatrix_sandwich_posSemidef_of_mul_eq_self
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    {P : Matrix (Fin D) (Fin D) ℂ} {X : Matrix (Fin D) (Fin k) ℂ}
    (hPX : P * X = X)
    (hP : (rightTensorMatrix P * choiMatrix T * (rightTensorMatrix P)ᴴ).PosSemidef) :
    (rightCompression T X).PosSemidef := by
  rw [← rightTensorMatrix_mul_choiMatrix_mul_conjTranspose]
  have hR : rightTensorMatrix X * rightTensorMatrix P = rightTensorMatrix X := by
    rw [rightTensorMatrix_mul_rightTensorMatrix, hPX]
  rw [← hR]
  simpa [Matrix.mul_assoc] using hP.conjTranspose_mul_mul_same (rightTensorMatrix X)ᴴ

/-- Converse projection-compression implication in Wolf, Proposition 3.1,
item 2.  If every rank-`k` Hermitian projection gives a positive Choi sandwich
and `k ≤ D`, then `T` is `k`-positive. -/
theorem isNPositiveMap_of_forall_rankProjection_rightTensor_choiMatrix_sandwich_posSemidef
    [NeZero D]
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hkD : k ≤ D)
    (hP : ∀ P : Matrix (Fin D) (Fin D) ℂ,
      P.IsHermitian → P * P = P → P.rank = k →
        (rightTensorMatrix P * choiMatrix T * (rightTensorMatrix P)ᴴ).PosSemidef) :
    IsNPositiveMap k T := by
  rw [isNPositiveMap_iff_forall_rightCompression_posSemidef]
  intro X
  obtain ⟨P, hHerm, hIdem, hrank, hPX⟩ :=
    Matrix.exists_isHermitian_idempotent_rank_mul_eq_self hkD X
  exact rightCompression_posSemidef_of_rightTensorMatrix_sandwich_posSemidef_of_mul_eq_self
    hPX (hP P hHerm hIdem hrank)

/-- Wolf's rank-`k` projection form of the Choi criterion: under `D > 0` and
`k ≤ D`, `k`-positivity is equivalent to positivity of all Choi sandwiches by
rank-`k` Hermitian idempotent right projections. -/
theorem isNPositiveMap_iff_forall_rankProjection_rightTensor_choiMatrix_sandwich_posSemidef
    [NeZero D]
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ} (hkD : k ≤ D) :
    IsNPositiveMap k T ↔
      ∀ P : Matrix (Fin D) (Fin D) ℂ,
        P.IsHermitian → P * P = P → P.rank = k →
          (rightTensorMatrix P * choiMatrix T * (rightTensorMatrix P)ᴴ).PosSemidef := by
  constructor
  · intro hT P hHerm hIdem hrank
    exact
      IsNPositiveMap.rightTensor_choiMatrix_sandwich_posSemidef_of_isHermitian_idempotent_rank
        hT hHerm hIdem hrank
  · exact
      isNPositiveMap_of_forall_rankProjection_rightTensor_choiMatrix_sandwich_posSemidef
        hkD

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

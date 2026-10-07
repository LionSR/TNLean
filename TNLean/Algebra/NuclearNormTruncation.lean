/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.Matrix

/-!
# Nuclear norms of rectangular matrices and low-rank truncation

For a finite rectangular complex matrix `M`, the nuclear norm is the sum of its singular values,
and the squared Hilbert--Schmidt norm is the sum of the squared moduli of its entries. This file
proves the two finite-dimensional estimates used in the whole-group tensor bound of the
polynomial-PEPS manuscript:

* the Hölder bound `‖A Bᵀ‖₁ ≤ ‖A‖₂ ‖B‖₂`;
* if `s₀ ≥ s₁ ≥ ⋯` are the singular values, then projecting onto the first `k` right singular
  directions leaves a squared Hilbert--Schmidt error `∑_{j ≥ k} s_j² ≤ ‖M‖₁² / (k + 1)`.

Both estimates are dimension free. The singular values are Mathlib's
`LinearMap.singularValues` of the Euclidean action of `M`, so the nuclear norm defined here
agrees with QICLean's square `Matrix.schattenOneNorm`. These generic matrix statements are
candidates for QICLean.

## Main definitions

* `Matrix.hsNormSq`: the squared Hilbert--Schmidt norm.
* `Matrix.nuclearNorm`: the sum of the singular values.
* `Matrix.orthonormalProjector`: the orthogonal projector onto the span of an orthonormal family.

## Main statements

* `Matrix.nuclearNorm_mul_transpose_le`: `‖A Bᵀ‖₁ ≤ ‖A‖₂ ‖B‖₂`.
* `Matrix.exists_orthonormal_truncation`: a rank-at-most-`k` right projection with squared
  Hilbert--Schmidt error at most `‖M‖₁² / (k + 1)`.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), Lemma 6.2 `lem:group-tensor`, proof,
  equation `eq:group-nuclear` and the singular-value tail estimate, 05-frames.tex:143–179.
-/

open scoped InnerProductSpace
open Module

noncomputable section

namespace Matrix

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- The squared Hilbert--Schmidt norm `∑ a b, |M a b|²` of a rectangular complex matrix. -/
def hsNormSq (M : Matrix α β ℂ) : ℝ := ∑ a, ∑ b, ‖M a b‖ ^ 2

theorem hsNormSq_nonneg (M : Matrix α β ℂ) : 0 ≤ hsNormSq M :=
  Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

theorem hsNormSq_transpose (M : Matrix α β ℂ) : hsNormSq Mᵀ = hsNormSq M := by
  unfold hsNormSq
  rw [Finset.sum_comm]
  rfl

theorem hsNormSq_conjTranspose (M : Matrix α β ℂ) : hsNormSq Mᴴ = hsNormSq M := by
  unfold hsNormSq
  rw [Finset.sum_comm]
  simp [conjTranspose_apply]

/-- Reindexing rows and columns by equivalences does not change the Hilbert--Schmidt norm. -/
theorem hsNormSq_submatrix {α' β' : Type*} [Fintype α'] [Fintype β'] (M : Matrix α β ℂ)
    (e₁ : α' ≃ α) (e₂ : β' ≃ β) : hsNormSq (M.submatrix e₁ e₂) = hsNormSq M := by
  unfold hsNormSq
  rw [← e₁.sum_comp]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  exact e₂.sum_comp fun b ↦ ‖M (e₁ a) b‖ ^ 2

section Euclidean

variable [DecidableEq β]

/-- The nuclear (trace) norm of a rectangular complex matrix: the sum of its singular values.

For square matrices indexed by `Fin D` this is QICLean's `Matrix.schattenOneNorm`. -/
def nuclearNorm (M : Matrix α β ℂ) : ℝ :=
  (toEuclideanLin M).singularValues.sum fun _ s ↦ s

omit [Fintype α] in
/-- The image of a Euclidean vector, row by row, is an inner product with the conjugated row. -/
theorem ofLp_toEuclideanLin_apply (X : Matrix α β ℂ) (x : EuclideanSpace ℂ β) (a : α) :
    (toEuclideanLin X x) a =
      ⟪(WithLp.toLp 2 fun b ↦ star (X a b) : EuclideanSpace ℂ β), x⟫_ℂ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [toLpLin_apply, mulVec, dotProduct, mul_comm]

/-- Bessel's inequality for the Hilbert--Schmidt norm: the squared images of an orthonormal family
have total size at most the squared Hilbert--Schmidt norm. -/
theorem sum_norm_sq_toEuclideanLin_le {ι : Type*} (s : Finset ι) (X : Matrix α β ℂ)
    {u : ι → EuclideanSpace ℂ β} (hu : Orthonormal ℂ u) :
    ∑ i ∈ s, ‖toEuclideanLin X (u i)‖ ^ 2 ≤ hsNormSq X := by
  have hrow : ∀ x : EuclideanSpace ℂ β, ‖toEuclideanLin X x‖ ^ 2 =
      ∑ a, ‖⟪x, (WithLp.toLp 2 fun b ↦ star (X a b) : EuclideanSpace ℂ β)⟫_ℂ‖ ^ 2 := by
    intro x
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [ofLp_toEuclideanLin_apply, norm_inner_symm]
  simp_rw [hrow]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun a _ ↦ ?_
  refine (hu.sum_inner_products_le _).trans_eq ?_
  rw [EuclideanSpace.norm_sq_eq]
  simp

/-- Parseval's identity for the Hilbert--Schmidt norm in an orthonormal basis. -/
theorem sum_norm_sq_toEuclideanLin_basis {ι : Type*} [Fintype ι] (X : Matrix α β ℂ)
    (w : OrthonormalBasis ι ℂ (EuclideanSpace ℂ β)) :
    ∑ i, ‖toEuclideanLin X (w i)‖ ^ 2 = hsNormSq X := by
  have hrow : ∀ x : EuclideanSpace ℂ β, ‖toEuclideanLin X x‖ ^ 2 =
      ∑ a, ‖⟪x, (WithLp.toLp 2 fun b ↦ star (X a b) : EuclideanSpace ℂ β)⟫_ℂ‖ ^ 2 := by
    intro x
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [ofLp_toEuclideanLin_apply, norm_inner_symm]
  simp_rw [hrow]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [w.sum_sq_norm_inner_right, EuclideanSpace.norm_sq_eq]
  simp

/-! ### The right singular basis -/

/-- The right singular basis: the eigenvector basis of `Mᴴ M`, with eigenvalues in decreasing
order. -/
def rightSingularBasis (M : Matrix α β ℂ) :
    OrthonormalBasis (Fin (Fintype.card β)) ℂ (EuclideanSpace ℂ β) :=
  (toEuclideanLin M).isSymmetric_adjoint_comp_self.eigenvectorBasis finrank_euclideanSpace

theorem inner_toEuclideanLin_rightSingularBasis (M : Matrix α β ℂ)
    (i j : Fin (Fintype.card β)) :
    ⟪toEuclideanLin M (rightSingularBasis M i), toEuclideanLin M (rightSingularBasis M j)⟫_ℂ =
      if i = j then
        (((toEuclideanLin M).isSymmetric_adjoint_comp_self.eigenvalues
          finrank_euclideanSpace j : ℝ) : ℂ)
      else 0 := by
  rw [← LinearMap.adjoint_inner_right]
  have h := (toEuclideanLin M).isSymmetric_adjoint_comp_self.apply_eigenvectorBasis
    finrank_euclideanSpace j
  rw [LinearMap.comp_apply] at h
  rw [rightSingularBasis, h, inner_smul_right, OrthonormalBasis.inner_eq_ite]
  split_ifs <;> simp

theorem norm_sq_toEuclideanLin_rightSingularBasis (M : Matrix α β ℂ)
    (i : Fin (Fintype.card β)) :
    ‖toEuclideanLin M (rightSingularBasis M i)‖ ^ 2 =
      (toEuclideanLin M).isSymmetric_adjoint_comp_self.eigenvalues finrank_euclideanSpace i := by
  have h := inner_toEuclideanLin_rightSingularBasis M i i
  simp only [↓reduceIte, inner_self_eq_norm_sq_to_K] at h
  exact Complex.ofReal_injective (by rw [Complex.ofReal_pow]; exact h)

/-- The singular values are the lengths of the images of the right singular basis. -/
theorem singularValues_eq_norm (M : Matrix α β ℂ) (i : Fin (Fintype.card β)) :
    (toEuclideanLin M).singularValues i = ‖toEuclideanLin M (rightSingularBasis M i)‖ := by
  rw [LinearMap.singularValues_fin _ finrank_euclideanSpace,
    ← norm_sq_toEuclideanLin_rightSingularBasis, Real.sqrt_sq (norm_nonneg _)]

theorem nuclearNorm_eq_sum_range (M : Matrix α β ℂ) :
    nuclearNorm M = ∑ i ∈ Finset.range (Fintype.card β), (toEuclideanLin M).singularValues i := by
  unfold nuclearNorm
  refine Finsupp.sum_of_support_subset _ ?_ _ fun _ _ ↦ rfl
  intro i hi
  rw [Finsupp.mem_support_iff] at hi
  rw [Finset.mem_range]
  by_contra h
  exact hi ((toEuclideanLin M).singularValues_of_finrank_le
    (by rw [finrank_euclideanSpace]; omega))

/-- The nuclear norm is the sum of the lengths of the images of the right singular basis. -/
theorem nuclearNorm_eq_sum_norm (M : Matrix α β ℂ) :
    nuclearNorm M = ∑ i, ‖toEuclideanLin M (rightSingularBasis M i)‖ := by
  rw [nuclearNorm_eq_sum_range, Finset.sum_range]
  exact Finset.sum_congr rfl fun i _ ↦ singularValues_eq_norm M i

theorem nuclearNorm_nonneg (M : Matrix α β ℂ) : 0 ≤ nuclearNorm M := by
  rw [nuclearNorm_eq_sum_norm]
  exact Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

/-! ### Hölder's bound -/

variable [DecidableEq γ]

/-- Hölder's inequality `‖A Bᵀ‖₁ ≤ ‖A‖₂ ‖B‖₂`. No dimension enters.

Polynomial-PEPS manuscript (Sept 24 2026), Lemma 6.2 `lem:group-tensor`, equation
`eq:group-nuclear`, 05-frames.tex:162–169. -/
theorem nuclearNorm_mul_transpose_le (A : Matrix α γ ℂ) (B : Matrix β γ ℂ) :
    nuclearNorm (A * Bᵀ) ≤ √(hsNormSq A) * √(hsNormSq B) := by
  classical
  set M := A * Bᵀ with hM
  set T := toEuclideanLin M
  set w := rightSingularBasis M
  set t : Fin (Fintype.card β) → ℝ := fun i ↦ ‖T (w i)‖ with ht
  -- normalized images of the singular basis
  set u : Fin (Fintype.card β) → EuclideanSpace ℂ α := fun i ↦ ((t i)⁻¹ : ℂ) • T (w i) with hu
  have hTsplit : ∀ x, T x = toEuclideanLin A (toEuclideanLin Bᵀ x) := by
    intro x
    simp only [T, hM, toLpLin_mul_same, LinearMap.comp_apply]
  have hadj : ∀ y x, ⟪y, toEuclideanLin A x⟫_ℂ = ⟪toEuclideanLin Aᴴ y, x⟫_ℂ := by
    intro y x
    rw [toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_left]
  -- the key pointwise estimate
  have hpt : ∀ i, t i ≤ ‖toEuclideanLin Aᴴ (u i)‖ * ‖toEuclideanLin Bᵀ (w i)‖ := by
    intro i
    rcases eq_or_lt_of_le (norm_nonneg (T (w i))) with h0 | hpos
    · rw [ht]
      dsimp only
      rw [← h0]
      positivity
    have hsq : t i ^ 2 ≤ ‖toEuclideanLin Aᴴ (T (w i))‖ * ‖toEuclideanLin Bᵀ (w i)‖ := by
      have h1 : (t i : ℂ) ^ 2 = ⟪toEuclideanLin Aᴴ (T (w i)), toEuclideanLin Bᵀ (w i)⟫_ℂ := by
        rw [← hadj, ← hTsplit, inner_self_eq_norm_sq_to_K]
        rfl
      have h2 : t i ^ 2 = ‖⟪toEuclideanLin Aᴴ (T (w i)), toEuclideanLin Bᵀ (w i)⟫_ℂ‖ := by
        rw [← h1]
        simp [norm_pow, Complex.norm_real, t]
      rw [h2]
      exact norm_inner_le_norm _ _
    have hu' : toEuclideanLin Aᴴ (u i) = ((t i)⁻¹ : ℂ) • toEuclideanLin Aᴴ (T (w i)) := by
      simp [hu]
    rw [hu', norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    have htpos : 0 < t i := hpos
    rw [mul_assoc, le_inv_mul_iff₀ htpos, ← sq]
    exact hsq
  -- orthonormality of the normalized images on the nonzero indices
  set s := Finset.univ.filter fun i : Fin (Fintype.card β) ↦ t i ≠ 0 with hs
  have horth : Orthonormal ℂ fun i : s ↦ u i := by
    rw [orthonormal_iff_ite]
    intro i j
    have hi : t i ≠ 0 := (Finset.mem_filter.mp i.2).2
    change ⟪((t i)⁻¹ : ℂ) • T (w i), ((t j)⁻¹ : ℂ) • T (w j)⟫_ℂ = _
    rw [inner_smul_left, inner_smul_right, inner_toEuclideanLin_rightSingularBasis]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte, ← norm_sq_toEuclideanLin_rightSingularBasis]
      change (starRingEnd ℂ) ((t i)⁻¹ : ℂ) * (((t i)⁻¹ : ℂ) * ((t i ^ 2 : ℝ) : ℂ)) = 1
      have : (t i : ℂ) ≠ 0 := by exact_mod_cast hi
      simp only [map_inv₀, Complex.conj_ofReal, Complex.ofReal_pow]
      field_simp
    · have hij' : (i : Fin (Fintype.card β)) ≠ j := fun h ↦ hij (Subtype.ext h)
      simp [hij, hij']
  have hsumA : ∑ i, ‖toEuclideanLin Aᴴ (u i)‖ ^ 2 ≤ hsNormSq A := by
    have hzero : ∀ i ∉ s, ‖toEuclideanLin Aᴴ (u i)‖ ^ 2 = 0 := by
      intro i hi
      have : t i = 0 := by simpa [hs] using hi
      simp [hu, this]
    rw [← Finset.sum_subset (Finset.subset_univ s) fun i _ hi ↦ hzero i hi,
      ← Finset.sum_coe_sort s, ← hsNormSq_conjTranspose A]
    exact sum_norm_sq_toEuclideanLin_le Finset.univ Aᴴ (u := fun i : s ↦ u i) horth
  have hsumB : ∑ i, ‖toEuclideanLin Bᵀ (w i)‖ ^ 2 = hsNormSq B := by
    rw [sum_norm_sq_toEuclideanLin_basis, hsNormSq_transpose]
  rw [nuclearNorm_eq_sum_norm]
  calc ∑ i, t i ≤ ∑ i, ‖toEuclideanLin Aᴴ (u i)‖ * ‖toEuclideanLin Bᵀ (w i)‖ :=
        Finset.sum_le_sum fun i _ ↦ hpt i
    _ ≤ √(∑ i, ‖toEuclideanLin Aᴴ (u i)‖ ^ 2) * √(∑ i, ‖toEuclideanLin Bᵀ (w i)‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ √(hsNormSq A) * √(hsNormSq B) := by
        rw [hsumB]
        gcongr

/-! ### Truncation to the leading right singular directions -/

omit [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ] in
/-- The singular-value tail estimate: for a decreasing nonnegative sequence `s`,
`(k + 1) ∑_{i ≥ k} sᵢ² ≤ (∑ᵢ sᵢ)²`.

Polynomial-PEPS manuscript (Sept 24 2026), proof of Lemma 6.2 `lem:group-tensor`,
05-frames.tex:170–176. -/
theorem tail_sq_sum_le (s : ℕ → ℝ) (hs : Antitone s) (h0 : ∀ i, 0 ≤ s i) (n k : ℕ) :
    (k + 1) * ∑ i ∈ Finset.range n, (if k ≤ i then s i ^ 2 else 0) ≤
      (∑ i ∈ Finset.range n, s i) ^ 2 := by
  set C := ∑ i ∈ Finset.range n, s i with hCdef
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ ↦ h0 i
  by_cases hkn : n ≤ k
  · have hzero : ∑ i ∈ Finset.range n, (if k ≤ i then s i ^ 2 else 0) = 0 :=
      Finset.sum_eq_zero fun i hi ↦ by
        rw [Finset.mem_range] at hi
        exact ite_eq_right_iff.mpr fun h ↦ absurd h (by omega)
    rw [hzero, mul_zero]
    positivity
  rw [not_le] at hkn
  have h1 : ∑ i ∈ Finset.range n, (if k ≤ i then s i ^ 2 else 0) ≤ s k * C := by
    calc ∑ i ∈ Finset.range n, (if k ≤ i then s i ^ 2 else 0)
        ≤ ∑ i ∈ Finset.range n, s k * s i := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          split_ifs with h
          · rw [sq]
            exact mul_le_mul_of_nonneg_right (hs h) (h0 i)
          · exact mul_nonneg (h0 k) (h0 i)
      _ = s k * C := by rw [Finset.mul_sum]
  have h2 : (k + 1) * s k ≤ C := by
    calc ((k : ℝ) + 1) * s k = ∑ _i ∈ Finset.range (k + 1), s k := by simp
      _ ≤ ∑ i ∈ Finset.range (k + 1), s i :=
          Finset.sum_le_sum fun i hi ↦ hs (by rw [Finset.mem_range] at hi; omega)
      _ ≤ C := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr (by omega)) fun i _ _ ↦ h0 i
  calc ((k : ℝ) + 1) * ∑ i ∈ Finset.range n, (if k ≤ i then s i ^ 2 else 0)
      ≤ (k + 1) * (s k * C) := by gcongr
    _ = ((k + 1) * s k) * C := by ring
    _ ≤ C * C := by gcongr
    _ = C ^ 2 := by ring

omit [Fintype γ] [DecidableEq γ] in
omit [Fintype α] in
/-- The orthogonal projector `∑ᵢ fᵢ fᵢ*` onto the span of a finite orthonormal family. -/
def orthonormalProjector {ι : Type*} [Fintype ι] (f : ι → EuclideanSpace ℂ β) :
    Matrix β β ℂ :=
  fun b b' ↦ ∑ i, f i b * star (f i b')

omit [Fintype α] [Fintype γ] [DecidableEq γ] in
theorem toEuclideanLin_orthonormalProjector {ι : Type*} [Fintype ι]
    (f : ι → EuclideanSpace ℂ β) (x : EuclideanSpace ℂ β) :
    toEuclideanLin (orthonormalProjector f) x = ∑ i, ⟪f i, x⟫_ℂ • f i := by
  ext b
  simp only [toLpLin_apply, PiLp.toLp_apply, mulVec, dotProduct, orthonormalProjector,
    EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Pi.star_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun b' _ ↦ by ring

omit [Fintype γ] [DecidableEq γ] in
/-- Truncation to the leading right singular directions. For every `k`, some orthonormal family
of at most `k` vectors has projector `P` with `(k + 1) ‖M - M P‖₂² ≤ ‖M‖₁²`; when the column
space has dimension at most `k`, the error vanishes. No dimension enters the estimate.

Polynomial-PEPS manuscript (Sept 24 2026), proof of Lemma 6.2 `lem:group-tensor`,
05-frames.tex:170–176. -/
theorem exists_orthonormal_truncation (M : Matrix α β ℂ) (k : ℕ) :
    ∃ r ≤ k, ∃ f : Fin r → EuclideanSpace ℂ β, Orthonormal ℂ f ∧
      (k + 1) * hsNormSq (M - M * orthonormalProjector f) ≤ nuclearNorm M ^ 2 ∧
      (Fintype.card β ≤ k → hsNormSq (M - M * orthonormalProjector f) = 0) := by
  classical
  set n := Fintype.card β
  set w := rightSingularBasis M
  set T := toEuclideanLin M
  let emb : Fin (min k n) → Fin n := Fin.castLE (min_le_right k n)
  set f : Fin (min k n) → EuclideanSpace ℂ β := fun i ↦ w (emb i) with hf
  have hforth : Orthonormal ℂ f := w.orthonormal.comp emb (Fin.castLE_injective _)
  have hproj : ∀ j : Fin n, toEuclideanLin (orthonormalProjector f) (w j) =
      if (j : ℕ) < k then w j else 0 := by
    intro j
    rw [toEuclideanLin_orthonormalProjector]
    simp only [hf, w.inner_eq_ite]
    by_cases hj : (j : ℕ) < k
    · rw [ite_eq_left_iff.mpr fun h ↦ absurd hj h, Finset.sum_eq_single ⟨j, lt_min hj j.2⟩]
      · simp [emb]
      · intro i _ hi
        have : emb i ≠ j := fun h ↦ hi (Fin.ext (by simpa [emb] using congrArg Fin.val h))
        simp [this]
      · simp
    · rw [ite_eq_right_iff.mpr fun h ↦ absurd h hj]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      have : emb i ≠ j := by
        intro h
        have h1 := congrArg Fin.val h
        simp only [emb, Fin.val_castLE] at h1
        have := i.2
        omega
      simp [this]
  have herr : hsNormSq (M - M * orthonormalProjector f) =
      ∑ i ∈ Finset.range n, (if k ≤ i then (T.singularValues i) ^ 2 else 0) := by
    rw [← sum_norm_sq_toEuclideanLin_basis _ w, Finset.sum_range]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [singularValues_eq_norm]
    have hsub : toEuclideanLin (M - M * orthonormalProjector f) (w j) =
        T (w j) - T (toEuclideanLin (orthonormalProjector f) (w j)) := by
      simp [T, toLpLin_mul_same]
    rw [hsub, hproj]
    by_cases hj : (j : ℕ) < k
    · simp [hj, Nat.not_le.mpr hj]
    · simp [hj, Nat.le_of_not_lt hj]
      rfl
  refine ⟨min k n, min_le_left k n, f, hforth, ?_, ?_⟩
  · rw [herr, nuclearNorm_eq_sum_range]
    exact tail_sq_sum_le _ (LinearMap.singularValues_antitone _)
      (LinearMap.singularValues_nonneg _) n k
  · intro hnk
    rw [herr]
    exact Finset.sum_eq_zero fun i hi ↦ by
        rw [Finset.mem_range] at hi
        exact ite_eq_right_iff.mpr fun h ↦ absurd h (by omega)

end Euclidean

end Matrix

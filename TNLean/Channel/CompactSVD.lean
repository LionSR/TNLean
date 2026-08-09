/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.SchmidtDecomposition

/-!
# Compact singular-value decomposition

This file packages the compact singular-value decomposition of a rectangular complex matrix.  The
intermediate space has dimension exactly the matrix rank, so every retained singular value is
strictly positive and the diagonal factor has an explicit two-sided inverse.

The orientation follows the convention in the matrix-product-unitary source:
`M = Vᴴ * D * U`, with `V * Vᴴ = U * Uᴴ = 1`.  This is the rank-truncated form of the rectangular
Schmidt-decomposition argument in `TNLean.Channel.SchmidtDecomposition`.

## Main declarations

* `Matrix.CompactSVD`: rank-indexed compact SVD data.
* `Matrix.exists_compactSVD`: existence for every finite rectangular complex matrix.

## References

* [arXiv:1703.09188, `II_SVD`, `eq:sf-svd`, and `YZ=1`, lines 461--508]
-/

open scoped Matrix InnerProductSpace ComplexOrder

namespace Matrix

variable {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ)

/-- A compact singular-value decomposition of `M`, indexed by `Fin M.rank`.

The factor orientation and row-coisometry identities are those of arXiv:1703.09188,
`eq:sf-svd` (lines 479--486).  Only strictly positive singular values are retained. -/
structure CompactSVD where
  /-- The left row-coisometry in the convention `M = Vᴴ * D * U`. -/
  V : Matrix (Fin M.rank) (Fin m) ℂ
  /-- The right row-coisometry in the convention `M = Vᴴ * D * U`. -/
  U : Matrix (Fin M.rank) (Fin n) ℂ
  /-- The positive singular values, with no zero padding. -/
  singularValues : Fin M.rank → ℝ
  singularValues_pos : ∀ i, 0 < singularValues i
  factorization : M = Vᴴ * Matrix.diagonal (fun i ↦ (singularValues i : ℂ)) * U
  V_mul_conjTranspose : V * Vᴴ = 1
  U_mul_conjTranspose : U * Uᴴ = 1

namespace CompactSVD

variable {M}

/-- The positive diagonal factor in a compact SVD. -/
noncomputable def diagonal (S : CompactSVD M) : Matrix (Fin M.rank) (Fin M.rank) ℂ :=
  Matrix.diagonal fun i ↦ (S.singularValues i : ℂ)

/-- The positive reciprocals of the retained singular values. -/
noncomputable def inverseSingularValues (S : CompactSVD M) (i : Fin M.rank) : ℝ :=
  (S.singularValues i)⁻¹

/-- Every inverse singular value is strictly positive. -/
theorem inverseSingularValues_pos (S : CompactSVD M) (i : Fin M.rank) :
    0 < S.inverseSingularValues i :=
  inv_pos.mpr (S.singularValues_pos i)

/-- The inverse positive diagonal factor from arXiv:1703.09188, `YZ=1` (lines 495--506). -/
noncomputable def inverseDiagonal (S : CompactSVD M) : Matrix (Fin M.rank) (Fin M.rank) ℂ :=
  Matrix.diagonal fun i ↦ (S.inverseSingularValues i : ℂ)

/-- The retained diagonal factor is positive definite. -/
theorem diagonal_posDef (S : CompactSVD M) : S.diagonal.PosDef := by
  rw [diagonal, Matrix.posDef_diagonal_iff]
  intro i
  exact_mod_cast S.singularValues_pos i

/-- The inverse diagonal factor is positive definite. -/
theorem inverseDiagonal_posDef (S : CompactSVD M) : S.inverseDiagonal.PosDef := by
  rw [inverseDiagonal, Matrix.posDef_diagonal_iff]
  intro i
  exact_mod_cast S.inverseSingularValues_pos i

/-- The factorization written using the packaged diagonal factor. -/
theorem factorization_diagonal (S : CompactSVD M) : M = S.Vᴴ * S.diagonal * S.U :=
  S.factorization

/-- The positive diagonal factor times its packaged inverse is the identity
(arXiv:1703.09188, `YZ=1`, lines 503--506). -/
@[simp]
theorem diagonal_mul_inverseDiagonal (S : CompactSVD M) : S.diagonal * S.inverseDiagonal = 1 := by
  rw [diagonal, inverseDiagonal, Matrix.diagonal_mul_diagonal]
  apply Matrix.diagonal_eq_one.mpr
  funext i
  rw [inverseSingularValues, Complex.ofReal_inv]
  exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (S.singularValues_pos i).ne')

/-- The packaged inverse times the positive diagonal factor is the identity
(arXiv:1703.09188, `YZ=1`, lines 503--506). -/
@[simp]
theorem inverseDiagonal_mul_diagonal (S : CompactSVD M) : S.inverseDiagonal * S.diagonal = 1 := by
  rw [diagonal, inverseDiagonal, Matrix.diagonal_mul_diagonal]
  apply Matrix.diagonal_eq_one.mpr
  funext i
  rw [inverseSingularValues, Complex.ofReal_inv]
  exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (S.singularValues_pos i).ne')

end CompactSVD

/-- Every finite rectangular complex matrix has a compact SVD indexed by its actual rank.

This is the unpadded rectangular SVD used in arXiv:1703.09188, `II_SVD` and `eq:sf-svd`
(lines 461--486).  The proof restricts the rectangular Schmidt decomposition to its nonzero
coefficients; their cardinality is exactly `M.rank`. -/
theorem exists_compactSVD : Nonempty (CompactSVD M) := by
  classical
  let ψ : Fin m × Fin n → ℂ := fun p ↦ M p.1 p.2
  obtain ⟨e, f, lam, hlam0, hψ, hnorm⟩ := exists_isSchmidtDecomposition ψ
  have hcoeff : schmidtCoeffMatrix ψ = M := by
    ext i j
    rfl
  have hrank : M.rank = Fintype.card {j // lam j ≠ 0} := by
    rw [← hcoeff, ← schmidtRank]
    exact IsSchmidtDecomposition.schmidtRank_eq_card_ne_zero ⟨hlam0, hψ, hnorm⟩
  let q : Fin M.rank ≃ {j // lam j ≠ 0} :=
    Fintype.equivOfCardEq (by simp [hrank])
  let leftIndex : Fin M.rank → Fin m :=
    fun i ↦ (q i).1.castLE (min_le_left m n)
  let rightIndex : Fin M.rank → Fin n :=
    fun i ↦ (q i).1.castLE (min_le_right m n)
  have hleft : Function.Injective leftIndex := by
    intro i j hij
    apply q.injective
    apply Subtype.ext
    exact Fin.castLE_injective (min_le_left m n) hij
  have hright : Function.Injective rightIndex := by
    intro i j hij
    apply q.injective
    apply Subtype.ext
    exact Fin.castLE_injective (min_le_right m n) hij
  let E : Matrix (Fin m) (Fin M.rank) ℂ := Matrix.of fun a i ↦ e (leftIndex i) a
  let F : Matrix (Fin n) (Fin M.rank) ℂ := Matrix.of fun b i ↦ f (rightIndex i) b
  let V : Matrix (Fin M.rank) (Fin m) ℂ := Eᴴ
  let U : Matrix (Fin M.rank) (Fin n) ℂ := Fᵀ
  let s : Fin M.rank → ℝ := fun i ↦ Real.sqrt (lam (q i).1)
  have hspos : ∀ i, 0 < s i := by
    intro i
    exact Real.sqrt_pos.mpr ((hlam0 _).lt_of_ne (Ne.symm (q i).2))
  have hfactor : M = Vᴴ * Matrix.diagonal (fun i ↦ (s i : ℂ)) * U := by
    ext a b
    rw [show M a b = ψ (a, b) by rfl, hψ a b]
    have hsum :
        (∑ j : Fin (min m n), (Real.sqrt (lam j) : ℂ) *
          e (j.castLE (min_le_left m n)) a * f (j.castLE (min_le_right m n)) b) =
        ∑ i : Fin M.rank, (Real.sqrt (lam (q i).1) : ℂ) *
          e (leftIndex i) a * f (rightIndex i) b := by
      have hsplit :
          (∑ j : {j // lam j ≠ 0}, (Real.sqrt (lam j.1) : ℂ) *
            e (j.1.castLE (min_le_left m n)) a *
              f (j.1.castLE (min_le_right m n)) b) +
          ∑ j : {j // ¬lam j ≠ 0}, (Real.sqrt (lam j.1) : ℂ) *
            e (j.1.castLE (min_le_left m n)) a *
              f (j.1.castLE (min_le_right m n)) b =
          ∑ j : Fin (min m n), (Real.sqrt (lam j) : ℂ) *
            e (j.castLE (min_le_left m n)) a * f (j.castLE (min_le_right m n)) b := by
        simpa using Fintype.sum_subtype_add_sum_subtype (p := fun j ↦ lam j ≠ 0)
          (fun j ↦ (Real.sqrt (lam j) : ℂ) * e (j.castLE (min_le_left m n)) a *
            f (j.castLE (min_le_right m n)) b)
      have hzero : ∑ j : {j // ¬lam j ≠ 0},
          (Real.sqrt (lam j.1) : ℂ) * e (j.1.castLE (min_le_left m n)) a *
            f (j.1.castLE (min_le_right m n)) b = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        simp [not_ne_iff.mp j.2]
      rw [← hsplit, hzero, add_zero]
      refine Fintype.sum_equiv q.symm
        (fun j : {j // lam j ≠ 0} ↦ (Real.sqrt (lam j.1) : ℂ) *
          e (j.1.castLE (min_le_left m n)) a * f (j.1.castLE (min_le_right m n)) b)
        (fun i : Fin M.rank ↦ (Real.sqrt (lam (q i).1) : ℂ) *
          e (leftIndex i) a * f (rightIndex i) b) fun j ↦ ?_
      simp only [leftIndex, rightIndex, Equiv.apply_symm_apply]
    rw [hsum]
    simp only [V, U, E, F, s, Matrix.mul_apply, Matrix.diagonal_apply,
      Matrix.conjTranspose_conjTranspose, Matrix.transpose_apply, Matrix.of_apply, mul_ite,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hV : V * Vᴴ = 1 := by
    rw [show V = Eᴴ by rfl, Matrix.conjTranspose_conjTranspose]
    exact conjTranspose_mul_eq_one_of_orthonormal hleft e
  have hU : U * Uᴴ = 1 := by
    exact transpose_mul_conjTranspose_eq_one_of_orthonormal hright f
  exact ⟨⟨V, U, s, hspos, hfactor, hV, hU⟩⟩

end Matrix

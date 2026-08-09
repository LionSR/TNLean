/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Compact singular-value decomposition

This file packages the compact singular-value decomposition of a rectangular complex matrix.  The
intermediate space has dimension exactly the matrix rank, so every retained singular value is
strictly positive and the diagonal factor has an explicit two-sided inverse.

The orientation follows the convention in the matrix-product-unitary source:
`M = Vᴴ * D * U`, with `V * Vᴴ = U * Uᴴ = 1`.  This is the rank-truncated rectangular
spectral-decomposition argument used for the Schmidt decomposition in
`TNLean.Channel.SchmidtDecomposition`.

## Main definitions

* `Matrix.CompactSVD`: rank-indexed compact SVD data.
* `Matrix.CompactSVD.diagonal`: the positive diagonal singular-value factor.
* `Matrix.CompactSVD.inverseDiagonal`: its positive diagonal inverse.

## Main results

* `Matrix.exists_compactSVD`: existence for every finite rectangular complex matrix.
* `Matrix.CompactSVD.diagonal_mul_inverseDiagonal`: the right inverse identity.
* `Matrix.CompactSVD.inverseDiagonal_mul_diagonal`: the left inverse identity.

## References

* [arXiv:1703.09188, `II_SVD`, `eq:sf-svd`, and `YZ=1`, lines 461--508]
-/

open scoped Matrix InnerProductSpace ComplexOrder

namespace Matrix

private theorem compact_conjTranspose_mul_eq_one_of_orthonormal
    {ι : Type*} [DecidableEq ι] {d : ℕ} {φ : ι → Fin d}
    (hφ : Function.Injective φ)
    (g : OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d))) :
    (Matrix.of fun a j ↦ g (φ j) a)ᴴ * (Matrix.of fun a j ↦ g (φ j) a) = 1 := by
  ext j k
  have hinner : ∑ a : Fin d, star (g (φ j) a) * g (φ k) a = ⟪g (φ j), g (φ k)⟫_ℂ := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Pi.star_apply, mul_comm]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
  rw [hinner, orthonormal_iff_ite.mp g.orthonormal (φ j) (φ k)]
  simp only [hφ.eq_iff]

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
(lines 461--486).  The proof applies the spectral theorem to `M * Mᴴ`, restricts to its
positive eigenvalues, and normalizes their images under `Mᴴ`; the number retained is exactly
`M.rank`. -/
theorem exists_compactSVD : Nonempty (CompactSVD M) := by
  classical
  set A : Matrix (Fin m) (Fin m) ℂ := M * Mᴴ with hAdef
  have hA : A.PosSemidef := by
    rw [hAdef]
    exact posSemidef_self_mul_conjTranspose M
  set e := hA.isHermitian.eigenvectorBasis with he
  set lam : Fin m → ℝ := hA.isHermitian.eigenvalues with hlam
  set w : Fin m → EuclideanSpace ℂ (Fin n) :=
    fun j ↦ WithLp.toLp 2 (Mᴴ *ᵥ ⇑(e j)) with hw
  have hlam0 : ∀ j, 0 ≤ lam j := fun j ↦ hA.eigenvalues_nonneg j
  have hgram : ∀ j k, ⟪w j, w k⟫_ℂ = if j = k then (lam j : ℂ) else 0 := by
    intro j k
    have hstep : ⟪w j, w k⟫_ℂ = (lam k : ℂ) * ⟪e j, e k⟫_ℂ := by
      simp only [hw]
      rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm, Matrix.star_mulVec,
        Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
        ← hAdef, hA.isHermitian.mulVec_eigenvectorBasis k,
        RCLike.real_smul_eq_coe_smul (K := ℂ), dotProduct_smul, smul_eq_mul,
        EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
      rfl
    rw [hstep, orthonormal_iff_ite.mp e.orthonormal j k]
    by_cases hjk : j = k <;> simp [hjk]
  have hrank : M.rank = Fintype.card {j // lam j ≠ 0} := by
    calc
      M.rank = A.rank := by rw [hAdef, Matrix.rank_self_mul_conjTranspose]
      _ = Fintype.card {j // hA.isHermitian.eigenvalues j ≠ 0} :=
        hA.isHermitian.rank_eq_card_non_zero_eigs
      _ = Fintype.card {j // lam j ≠ 0} := by rw [hlam]
  let q : Fin M.rank ≃ {j // lam j ≠ 0} :=
    Fintype.equivOfCardEq (by simp [hrank])
  let leftIndex : Fin M.rank → Fin m := fun i ↦ (q i).1
  have hleft : Function.Injective leftIndex := by
    intro i j hij
    apply q.injective
    exact Subtype.ext hij
  let s : Fin M.rank → ℝ := fun i ↦ Real.sqrt (lam (q i).1)
  have hspos : ∀ i, 0 < s i := by
    intro i
    exact Real.sqrt_pos.mpr ((hlam0 _).lt_of_ne (Ne.symm (q i).2))
  let v : Fin M.rank → EuclideanSpace ℂ (Fin n) := fun i ↦
    WithLp.toLp 2 (star ((s i : ℂ)⁻¹ • ⇑(w (q i).1)))
  have hvOrthonormal : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    have hsreal : ∀ k, star (s k : ℂ) = (s k : ℂ) := fun k ↦ by
      rw [Complex.star_def, Complex.conj_ofReal]
    have hinner : ⟪v i, v j⟫_ℂ =
        ((s j : ℂ)⁻¹ * (s i : ℂ)⁻¹) * ⟪w (q j).1, w (q i).1⟫_ℂ := by
      simp only [v]
      rw [EuclideanSpace.inner_toLp_toLp, star_star, star_smul, smul_dotProduct,
        dotProduct_smul, star_inv₀, hsreal, dotProduct_comm,
        ← EuclideanSpace.inner_eq_star_dotProduct, smul_eq_mul, smul_eq_mul]
      ring
    rw [hinner, hgram]
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl, if_pos rfl]
      have hsne : (s i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hspos i).ne'
      have hsquare : (s i : ℂ) ^ 2 = (lam (q i).1 : ℂ) := by
        rw [show s i = Real.sqrt (lam (q i).1) by rfl, ← Complex.ofReal_pow,
          Real.sq_sqrt (hlam0 _)]
      field_simp
      exact hsquare.symm
    · have hqne : (q j).1 ≠ (q i).1 := by
        intro h
        exact hij (q.injective (Subtype.ext h.symm))
      rw [if_neg hqne, if_neg hij, mul_zero]
  let E : Matrix (Fin m) (Fin M.rank) ℂ := Matrix.of fun a i ↦ e (leftIndex i) a
  let V : Matrix (Fin M.rank) (Fin m) ℂ := Eᴴ
  let F : Matrix (Fin n) (Fin M.rank) ℂ := Matrix.of fun b i ↦ v i b
  let U : Matrix (Fin M.rank) (Fin n) ℂ := Fᵀ
  have hstar : ∀ x : Fin m → ℂ, star (Mᴴ *ᵥ x) = star x ᵥ* M := fun x ↦ by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
  have hcoeff : ∀ (j : Fin m) (b : Fin n),
      ⟪e j, WithLp.toLp 2 (M *ᵥ Pi.single b 1)⟫_ℂ = star ((w j).ofLp b) := by
    intro j b
    rw [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, dotProduct_comm,
      Matrix.dotProduct_mulVec, ← hstar, dotProduct_single_one]
    simp only [hw, WithLp.ofLp_toLp, Pi.star_apply]
  have hfull : ∀ a b, M a b = ∑ j : Fin m, e j a * star ((w j).ofLp b) := by
    intro a b
    have htoLp : WithLp.toLp 2 (M *ᵥ Pi.single b 1) =
        ∑ j : Fin m, star ((w j).ofLp b) • e j := by
      rw [← e.sum_repr' (WithLp.toLp 2 (M *ᵥ Pi.single b 1))]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [hcoeff j b]
    have hfun : M *ᵥ Pi.single b 1 =
        ∑ j : Fin m, star ((w j).ofLp b) • ⇑(e j) := by
      have h := congrArg (WithLp.addEquiv 2 (Fin m → ℂ)) htoLp
      rw [map_sum, WithLp.coe_addEquiv, WithLp.ofLp_toLp] at h
      rw [h]
      exact Finset.sum_congr rfl fun j _ ↦ WithLp.ofLp_smul _ _ _
    have happ := congrFun hfun a
    rw [Finset.sum_apply] at happ
    simp only [Pi.smul_apply, smul_eq_mul] at happ
    have hMab : M a b = (M *ᵥ Pi.single b 1) a := by
      rw [Matrix.mulVec_single_one]
      rfl
    rw [hMab, happ]
    exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
  have hwzero : ∀ j, lam j = 0 → w j = 0 := by
    intro j hj
    have hjj := hgram j j
    rw [if_pos rfl, hj, Complex.ofReal_zero] at hjj
    exact inner_self_eq_zero.mp hjj
  have hfactor : M = Vᴴ * Matrix.diagonal (fun i ↦ (s i : ℂ)) * U := by
    ext a b
    rw [hfull a b]
    have hsplit := Fintype.sum_subtype_add_sum_subtype
      (p := fun j ↦ lam j ≠ 0) (fun j ↦ e j a * star ((w j).ofLp b))
    have hzero : ∑ j : {j // ¬lam j ≠ 0},
        e j.1 a * star ((w j.1).ofLp b) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [hwzero j.1 (not_ne_iff.mp j.2)]
      simp
    rw [← hsplit, hzero, add_zero]
    refine (Fintype.sum_equiv q.symm
      (fun j : {j // lam j ≠ 0} ↦ e j.1 a * star ((w j.1).ofLp b))
      (fun i : Fin M.rank ↦ e (q i).1 a * star ((w (q i).1).ofLp b))
      (fun j ↦ by simp)).trans ?_
    simp only [V, U, E, F, Matrix.mul_apply, Matrix.diagonal_apply,
      Matrix.conjTranspose_conjTranspose, Matrix.transpose_apply, Matrix.of_apply, mul_ite,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, leftIndex]
    apply Finset.sum_congr rfl
    intro i _
    have hsne : (s i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hspos i).ne'
    simp only [v, Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul, star_inv₀]
    rw [show star (s i : ℂ) = (s i : ℂ) by
      rw [Complex.star_def, Complex.conj_ofReal]]
    field_simp
  have hV : V * Vᴴ = 1 := by
    rw [show V = Eᴴ by rfl, Matrix.conjTranspose_conjTranspose]
    exact compact_conjTranspose_mul_eq_one_of_orthonormal hleft e
  have hU : U * Uᴴ = 1 := by
    ext i j
    have hinner : ∑ b : Fin n, v i b * star (v j b) = ⟪v j, v i⟫_ℂ := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp only [dotProduct, Pi.star_apply]
    simp only [U, F, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
      Matrix.of_apply, hinner, orthonormal_iff_ite.mp hvOrthonormal,
      Matrix.one_apply, eq_comm]
  exact ⟨⟨V, U, s, hspos, hfactor, hV, hU⟩⟩

end Matrix

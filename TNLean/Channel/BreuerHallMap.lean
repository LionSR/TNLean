/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import TNLean.Algebra.MatrixAux
import TNLean.Channel.Basic
import TNLean.Algebra.MatrixSpectralDecomp

/-!
# Positivity of the Breuer-Hall map

This file records the **Breuer-Hall map**, one of the concrete positive maps of
Wolf Chapter 3, Example 3.1, equation (3.19).  For a fixed antisymmetric
contraction `U` on `M_D(ℂ)` it is the map
`T_BH(X) = (tr X) I - X - U Xᵀ Uᴴ`.

The main result `Matrix.breuerHallMap_isPositiveMap` shows that `T_BH` is a
positive map: it sends positive semidefinite matrices to positive semidefinite
matrices.

The proof reduces positivity to the rank-one case: a positive semidefinite
matrix is a sum of rank-one outer products `v vᴴ`, and on such a matrix
`T_BH(v vᴴ) = ‖v‖² I - v vᴴ - w wᴴ`, where `w = U *ᵥ star v` applies `U` to the
entrywise conjugate of `v`.  The two vectors `v` and `w` are orthogonal (by
antisymmetry of `U`) and `‖w‖ ≤ ‖v‖` (by the contraction property), so the
quadratic form is nonnegative by a two-vector form of Bessel's inequality.

Indecomposability of the Breuer-Hall map and the `n`-positivity threshold are
not treated here; only positivity is established.

## Main declarations

* `Matrix.breuerHallMap` -- the Breuer-Hall map `T_BH`.
* `Matrix.breuerHallMap_isPositiveMap` -- `T_BH` is a positive map.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 3,
  Example 3.1, equation (3.19)][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder InnerProductSpace
open Matrix

/-! ## A two-vector orthogonal Bessel inequality -/

section InnerProductAux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- For orthogonal vectors `x ⟂ y` with `‖y‖ ≤ ‖x‖`, the squared overlaps of any
`w` with `x` and `y` add up to at most `‖x‖² ‖w‖²`.  This is the two-vector form
of Bessel's inequality used to control the quadratic form of the Breuer-Hall
map. -/
theorem orthogonal_two_inner_normSq_le {x y : E} (hxy : ⟪x, y⟫_ℂ = 0)
    (hyx : ‖y‖ ≤ ‖x‖) (w : E) :
    ‖⟪x, w⟫_ℂ‖ ^ 2 + ‖⟪y, w⟫_ℂ‖ ^ 2 ≤ ‖x‖ ^ 2 * ‖w‖ ^ 2 := by
  set s : ℝ := ‖x‖ ^ 2 with hs
  have hs0 : 0 ≤ s := by positivity
  set g : E := (s : ℂ) • w - ⟪x, w⟫_ℂ • x with hg
  have hyx' : ⟪y, x⟫_ℂ = 0 := inner_eq_zero_symm.mp hxy
  have hyg : ⟪y, g⟫_ℂ = (s : ℂ) * ⟪y, w⟫_ℂ := by
    rw [hg, inner_sub_right, inner_smul_right, inner_smul_right, hyx', mul_zero, sub_zero]
  have hcross : ⟪(s : ℂ) • w, ⟪x, w⟫_ℂ • x⟫_ℂ = ((s * ‖⟪x, w⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_smul_left, inner_smul_right, ← inner_conj_symm w x, Complex.conj_ofReal,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  have hcrossre : RCLike.re (⟪(s : ℂ) • w, ⟪x, w⟫_ℂ • x⟫_ℂ) = s * ‖⟪x, w⟫_ℂ‖ ^ 2 := by
    rw [hcross]; exact Complex.ofReal_re _
  have hgnorm : ‖g‖ ^ 2 = s ^ 2 * ‖w‖ ^ 2 - s * ‖⟪x, w⟫_ℂ‖ ^ 2 := by
    have hxs : ‖x‖ ^ 2 = s := hs.symm
    rw [hg, norm_sub_sq (𝕜 := ℂ), hcrossre, norm_smul, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg hs0]
    linear_combination ‖⟪x, w⟫_ℂ‖ ^ 2 * hxs
  have hCSx : ‖⟪x, w⟫_ℂ‖ ^ 2 ≤ s * ‖w‖ ^ 2 := by
    have hCS := norm_inner_le_norm (𝕜 := ℂ) x w
    have hsq : ‖⟪x, w⟫_ℂ‖ ^ 2 ≤ (‖x‖ * ‖w‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hCS 2
    calc ‖⟪x, w⟫_ℂ‖ ^ 2 ≤ (‖x‖ * ‖w‖) ^ 2 := hsq
      _ = s * ‖w‖ ^ 2 := by rw [hs]; ring
  have hCSy : s ^ 2 * ‖⟪y, w⟫_ℂ‖ ^ 2 ≤ ‖y‖ ^ 2 * ‖g‖ ^ 2 := by
    have hCS := norm_inner_le_norm (𝕜 := ℂ) y g
    have hnorm : ‖⟪y, g⟫_ℂ‖ = s * ‖⟪y, w⟫_ℂ‖ := by
      rw [hyg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0]
    rw [hnorm] at hCS
    have hsq : (s * ‖⟪y, w⟫_ℂ‖) ^ 2 ≤ (‖y‖ * ‖g‖) ^ 2 := pow_le_pow_left₀ (by positivity) hCS 2
    nlinarith [hsq]
  rcases eq_or_lt_of_le hs0 with hs00 | hspos
  · have hxnorm : ‖x‖ = 0 := by
      have hx2 : ‖x‖ ^ 2 = 0 := by rw [← hs, ← hs00]
      nlinarith [norm_nonneg x]
    have hx0 : x = 0 := norm_eq_zero.mp hxnorm
    have hy0 : y = 0 := norm_eq_zero.mp (le_antisymm (by rw [hxnorm] at hyx; exact hyx)
      (norm_nonneg _))
    rw [hx0, hy0]
    simp [← hs00]
  · have hgnonneg : 0 ≤ ‖g‖ ^ 2 := by positivity
    have hyg2 : s ^ 2 * ‖⟪y, w⟫_ℂ‖ ^ 2 ≤ s * ‖g‖ ^ 2 := by
      have hys : ‖y‖ ^ 2 ≤ s := by rw [hs]; exact pow_le_pow_left₀ (norm_nonneg _) hyx 2
      calc s ^ 2 * ‖⟪y, w⟫_ℂ‖ ^ 2 ≤ ‖y‖ ^ 2 * ‖g‖ ^ 2 := hCSy
        _ ≤ s * ‖g‖ ^ 2 := by nlinarith [hgnonneg]
    rw [hgnorm] at hyg2
    have hkey : s ^ 2 * ‖⟪y, w⟫_ℂ‖ ^ 2 ≤ s ^ 2 * (s * ‖w‖ ^ 2 - ‖⟪x, w⟫_ℂ‖ ^ 2) := by
      nlinarith [hyg2]
    have hb : ‖⟪y, w⟫_ℂ‖ ^ 2 ≤ s * ‖w‖ ^ 2 - ‖⟪x, w⟫_ℂ‖ ^ 2 :=
      le_of_mul_le_mul_left hkey (by positivity)
    linarith

end InnerProductAux

namespace Matrix

variable {d : ℕ}

/-! ## The Breuer-Hall map -/

/-- **Wolf Chapter 3, Example 3.1, equation (3.19).** The Breuer-Hall map
`T_BH(X) = (tr X) I - X - U Xᵀ Uᴴ` on `M_D(ℂ)`, parametrised by a matrix `U`. -/
noncomputable def breuerHallMap (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ where
  toFun X := Matrix.trace X • (1 : Matrix (Fin d) (Fin d) ℂ) - X - U * Xᵀ * Uᴴ
  map_add' X Y := by
    simp only [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add, add_smul]
    abel
  map_smul' c X := by
    simp only [RingHom.id_apply, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.trace_smul, smul_sub, smul_smul, smul_eq_mul]

@[simp]
theorem breuerHallMap_apply (U : Matrix (Fin d) (Fin d) ℂ) (X : Matrix (Fin d) (Fin d) ℂ) :
    breuerHallMap U X =
      Matrix.trace X • (1 : Matrix (Fin d) (Fin d) ℂ) - X - U * Xᵀ * Uᴴ :=
  rfl

/-! ## Positivity on rank-one outer products -/

/-- On a rank-one outer product `v vᴴ`, the Breuer-Hall map is positive
semidefinite.  This is the key step in the positivity proof: with
`w = U *ᵥ star v` the image under `U` of the entrywise conjugate of `v`, the
image is `‖v‖² I - v vᴴ - w wᴴ`, whose quadratic form is nonnegative by the
two-vector Bessel inequality applied to the orthogonal pair `v ⟂ w` with
`‖w‖ ≤ ‖v‖`. -/
theorem breuerHallMap_vecMulVec_posSemidef (U : Matrix (Fin d) (Fin d) ℂ)
    (hUanti : Uᵀ = -U) (hUcontr : Uᴴ * U ≤ 1) (v : Fin d → ℂ) :
    (breuerHallMap U (Matrix.vecMulVec v (star v))).PosSemidef := by
  classical
  set p : Fin d → ℂ := U *ᵥ star v with hp
  set A : Matrix (Fin d) (Fin d) ℂ := Matrix.vecMulVec v (star v) with hA
  set B : Matrix (Fin d) (Fin d) ℂ := Matrix.vecMulVec p (star p) with hB
  -- the image is `tr A • 1 - A - B`
  have hUterm : U * Aᵀ * Uᴴ = B := by
    rw [hA, Matrix.transpose_vecMulVec, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hB, hp,
      Matrix.vecMul_conjTranspose]
  have hM : breuerHallMap U A = Matrix.trace A • (1 : Matrix (Fin d) (Fin d) ℂ) - A - B := by
    rw [breuerHallMap_apply, hUterm]
  rw [hM]
  -- inner-product avatars
  set V : EuclideanSpace ℂ (Fin d) := WithLp.toLp 2 v with hV
  set P : EuclideanSpace ℂ (Fin d) := WithLp.toLp 2 p with hP
  have bridge : ∀ a b : Fin d → ℂ,
      star a ⬝ᵥ b = ⟪(WithLp.toLp 2 a : EuclideanSpace ℂ (Fin d)), WithLp.toLp 2 b⟫_ℂ := by
    intro a b
    rw [EuclideanSpace.inner_toLp_toLp]
    exact dotProduct_comm (star a) b
  -- orthogonality `v ⟂ U *ᵥ star v`
  have hzero : star v ⬝ᵥ (U *ᵥ star v) = 0 := by
    have key : star v ⬝ᵥ (U *ᵥ star v) = -(star v ⬝ᵥ (U *ᵥ star v)) := by
      calc star v ⬝ᵥ (U *ᵥ star v)
          = (star v ᵥ* U) ⬝ᵥ star v := dotProduct_mulVec (star v) U (star v)
        _ = (Uᵀ *ᵥ star v) ⬝ᵥ star v := by rw [← Matrix.mulVec_transpose]
        _ = ((-U) *ᵥ star v) ⬝ᵥ star v := by rw [hUanti]
        _ = -((U *ᵥ star v) ⬝ᵥ star v) := by rw [Matrix.neg_mulVec, neg_dotProduct]
        _ = -(star v ⬝ᵥ (U *ᵥ star v)) := by rw [dotProduct_comm]
    rwa [eq_neg_iff_add_eq_zero, add_self_eq_zero] at key
  have horth : ⟪V, P⟫_ℂ = 0 := by
    rw [hV, hP, ← bridge v p, hp]; exact hzero
  -- contraction bound `‖U *ᵥ star v‖ ≤ ‖v‖`
  have hPV : ‖P‖ ≤ ‖V‖ := by
    have hpsd : (1 - Uᴴ * U).PosSemidef := by rw [← Matrix.le_iff]; exact hUcontr
    have hquad : (0 : ℂ) ≤ star (star v) ⬝ᵥ ((1 - Uᴴ * U) *ᵥ star v) :=
      hpsd.dotProduct_mulVec_nonneg _
    have hval : star (star v) ⬝ᵥ ((1 - Uᴴ * U) *ᵥ star v) = v ⬝ᵥ star v - star p ⬝ᵥ p := by
      rw [star_star, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub,
        ← Matrix.mulVec_mulVec, hp]
      congr 1
      rw [dotProduct_mulVec, Matrix.vecMul_conjTranspose]
    rw [hval] at hquad
    have hre : (star p ⬝ᵥ p).re ≤ (v ⬝ᵥ star v).re := by
      have hle := (Complex.le_def.mp hquad).1
      simpa using hle
    have hnP : ‖P‖ ^ 2 = (star p ⬝ᵥ p).re := by
      rw [hP, ← inner_self_eq_norm_sq (𝕜 := ℂ), EuclideanSpace.inner_toLp_toLp,
        dotProduct_comm p (star p)]
      rfl
    have hnV : ‖V‖ ^ 2 = (v ⬝ᵥ star v).re := by
      rw [hV, ← inner_self_eq_norm_sq (𝕜 := ℂ), EuclideanSpace.inner_toLp_toLp]
      rfl
    have hsq : ‖P‖ ^ 2 ≤ ‖V‖ ^ 2 := by rw [hnP, hnV]; exact hre
    nlinarith [norm_nonneg P, norm_nonneg V, hsq]
  -- now show PSD via the quadratic form
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · -- Hermitian
    have hAherm : A.IsHermitian := (Matrix.posSemidef_vecMulVec_self_star v).1
    have hcSA : IsSelfAdjoint (Matrix.trace A) := by
      rw [isSelfAdjoint_iff, ← Matrix.trace_conjTranspose, hAherm]
    exact ((isHermitian_one.smul hcSA).sub hAherm).sub
      (Matrix.posSemidef_vecMulVec_self_star p).1
  · intro w
    set W : EuclideanSpace ℂ (Fin d) := WithLp.toLp 2 w with hW
    -- expand the quadratic form
    have hQ : star w ⬝ᵥ ((Matrix.trace A • (1 : Matrix (Fin d) (Fin d) ℂ) - A - B) *ᵥ w) =
        Matrix.trace A * (star w ⬝ᵥ w) - (star v ⬝ᵥ w) * (star w ⬝ᵥ v)
          - (star p ⬝ᵥ w) * (star w ⬝ᵥ p) := by
      rw [Matrix.sub_mulVec, Matrix.sub_mulVec, dotProduct_sub, dotProduct_sub,
        Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul, hA, hB,
        star_dotProduct_vecMulVec_mulVec, star_dotProduct_vecMulVec_mulVec]
    rw [hQ]
    -- rewrite trace and overlaps as inner products
    have htr : Matrix.trace A = ⟪V, V⟫_ℂ := by
      rw [hA, Matrix.trace_vecMulVec, hV, EuclideanSpace.inner_toLp_toLp]
    have h1 : star v ⬝ᵥ w = ⟪V, W⟫_ℂ := by rw [hV, hW]; exact bridge v w
    have h2 : star w ⬝ᵥ v = ⟪W, V⟫_ℂ := by rw [hV, hW]; exact bridge w v
    have h3 : star w ⬝ᵥ w = ⟪W, W⟫_ℂ := by rw [hW]; exact bridge w w
    have h4 : star p ⬝ᵥ w = ⟪P, W⟫_ℂ := by rw [hP, hW]; exact bridge p w
    have h5 : star w ⬝ᵥ p = ⟪W, P⟫_ℂ := by rw [hP, hW]; exact bridge w p
    rw [htr, h1, h2, h3, h4, h5]
    -- collapse the products of conjugate inner products to squared norms
    have hVV : ⟪V, V⟫_ℂ = ((‖V‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]; norm_cast
    have hWW : ⟪W, W⟫_ℂ = ((‖W‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]; norm_cast
    have e1 : ⟪V, V⟫_ℂ * ⟪W, W⟫_ℂ = ((‖V‖ ^ 2 * ‖W‖ ^ 2 : ℝ) : ℂ) := by
      rw [hVV, hWW]; push_cast; ring
    have e2 : ⟪V, W⟫_ℂ * ⟪W, V⟫_ℂ = ((‖⟪V, W⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
      rw [← inner_conj_symm W V, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have e3 : ⟪P, W⟫_ℂ * ⟪W, P⟫_ℂ = ((‖⟪P, W⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
      rw [← inner_conj_symm W P, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [e1, e2, e3,
      show ((‖V‖ ^ 2 * ‖W‖ ^ 2 : ℝ) : ℂ) - ((‖⟪V, W⟫_ℂ‖ ^ 2 : ℝ) : ℂ)
          - ((‖⟪P, W⟫_ℂ‖ ^ 2 : ℝ) : ℂ)
        = ((‖V‖ ^ 2 * ‖W‖ ^ 2 - ‖⟪V, W⟫_ℂ‖ ^ 2 - ‖⟪P, W⟫_ℂ‖ ^ 2 : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.zero_le_real]
    have hbessel := orthogonal_two_inner_normSq_le horth hPV W
    linarith

/-! ## Positivity of the Breuer-Hall map -/

/-- **Wolf Chapter 3, Example 3.1, equation (3.19).** The Breuer-Hall map
`T_BH(X) = (tr X) I - X - U Xᵀ Uᴴ` of an antisymmetric contraction `U`
(`Uᵀ = -U` and `Uᴴ U ≤ 1`) is a positive map. -/
theorem breuerHallMap_isPositiveMap (U : Matrix (Fin d) (Fin d) ℂ)
    (hUanti : Uᵀ = -U) (hUcontr : Uᴴ * U ≤ 1) :
    IsPositiveMap (breuerHallMap U) := by
  classical
  intro X hX
  rw [hX.eq_sum_vecMulVec_nonzero_eigs, map_sum]
  refine Matrix.posSemidef_sum _ (fun i _ => ?_)
  exact breuerHallMap_vecMulVec_posSemidef U hUanti hUcontr _

end Matrix

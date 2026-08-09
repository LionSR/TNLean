/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Schwarz.TwoPositive
import TNLean.Channel.Schwarz.AbstractMultiplicativeDomain
import Mathlib.Data.Matrix.Block

/-!
# Two-variable operator Schwarz inequality

This file proves the two-variable operator Schwarz inequality for 2-positive
linear maps (Wolf, Theorem 5.3).

## Main results

* `schwarz_two_variable`: The two-variable operator Schwarz inequality: for a
  2-positive map `E` and all matrices `A, B`, for all vectors `v, w` with
  `E(B†B) w = E(B†A) v`, we have `v† E(A†A) v ≥ v† E(A†B) w`.  This is the
  pseudoinverse-free formulation of Wolf's Eq. (5.4).

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 5,
  Theorems 5.3][Wolf2012QChannels]
* Local source: `Notes/WolfNoteTexSource/ch05_schwarz_inequalities.tex`,
  lines 180--190.
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix Finset Complex

namespace SchwarzTwoVariable

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "Mat" => Matrix n n ℂ

omit [DecidableEq n] in
/-- The block matrix `C†C` for `C = [A B]` (horizontal concatenation) is PSD. -/
lemma blockMatrix_CtC_posSemidef (A B : Mat) :
    (Matrix.fromBlocks (Aᴴ * A) (Aᴴ * B) (Bᴴ * A) (Bᴴ * B) :
      Matrix (n ⊕ n) (n ⊕ n) ℂ).PosSemidef := by
  let C : Matrix n (n ⊕ n) ℂ := fun i j =>
    match j with
    | Sum.inl a => A i a
    | Sum.inr b => B i b
  have hC_sq : Cᴴ * C = Matrix.fromBlocks (Aᴴ * A) (Aᴴ * B) (Bᴴ * A) (Bᴴ * B) := by
    ext i j
    rcases i with (i | i) <;> rcases j with (j | j) <;>
      simp [C, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [← hC_sq]
  exact Matrix.posSemidef_conjTranspose_mul_self C

/-! ### 2-positivity ampliation of the block matrix -/

omit [DecidableEq n] in
/-- The 2-positivity ampliation applied to the block matrix `C†C` yields a PSD
`2×2` block matrix of the form `[[E(A†A), E(A†B)], [E(B†A), E(B†B)]]`. -/
lemma ampliated_block_matrix_posSemidef (E : Mat →ₗ[ℂ] Mat) (h2pos : Is2PositiveMap E)
    (A B : Mat) :
    (Matrix.fromBlocks (E (Aᴴ * A)) (E (Aᴴ * B)) (E (Bᴴ * A)) (E (Bᴴ * B)) :
      Matrix (n ⊕ n) (n ⊕ n) ℂ).PosSemidef := by
  let P : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
    Matrix.fromBlocks (Aᴴ * A) (Aᴴ * B) (Bᴴ * A) (Bᴴ * B)
  have hP : P.PosSemidef := blockMatrix_CtC_posSemidef A B
  let e : n × Fin 2 ≃ n ⊕ n := finTwoSumEquiv n
  let P' : Matrix (n × Fin 2) (n × Fin 2) ℂ := Matrix.reindex e.symm e.symm P
  have hP' : P'.PosSemidef := by
    simpa [P', Matrix.reindex_apply] using hP.submatrix e
  have hY' := h2pos P' hP'
  set Y : Matrix (n × Fin 2) (n × Fin 2) ℂ :=
    Matrix.of fun (ip : n × Fin 2) (jq : n × Fin 2) =>
      (E (Matrix.of fun i j => P' (i, ip.2) (j, jq.2))) ip.1 jq.1
    with hY_def
  have hY_psd : Y.PosSemidef := hY'
  let Q : Matrix (n ⊕ n) (n ⊕ n) ℂ := Matrix.reindex e e Y
  have hQ_psd : Q.PosSemidef := by
    have hsub := hY_psd.submatrix e.symm
    simpa [Q, Matrix.reindex_apply, Matrix.submatrix_apply] using hsub
  have hP'Block (p q : Fin 2) :
      Matrix.of (fun i j => P' (i, p) (j, q)) =
        match p, q with
        | 0, 0 => Aᴴ * A
        | 0, 1 => Aᴴ * B
        | 1, 0 => Bᴴ * A
        | 1, 1 => Bᴴ * B := by
    fin_cases p <;> fin_cases q <;>
      ext i j <;> simp [P', Matrix.reindex_apply, P, e, finTwoSumEquiv, finTwoEquiv]
  have hQ_eq : Q =
      Matrix.fromBlocks (E (Aᴴ * A)) (E (Aᴴ * B)) (E (Bᴴ * A)) (E (Bᴴ * B)) := by
    ext i j
    rcases i with (i | i) <;> rcases j with (j | j) <;>
      simp [Q, Y, hP'Block, e, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply]
  rw [hQ_eq] at hQ_psd
  exact hQ_psd

/-! ### Real-valued auxiliary lemmas -/

-- (Uses `linear_eq_zero_of_quadratic_nonneg` from AbstractMultiplicativeDomain)
omit [DecidableEq n] in
/-- A complex number `z† A z` for a PSD matrix `A` is nonnegative. -/
private lemma dotProduct_mulVec_nonneg_of_posSemidef_block {A C B : Mat}
    (h : (Matrix.fromBlocks A C Cᴴ B : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosSemidef)
    (z : n → ℂ) :
    0 ≤ star z ⬝ᵥ (A.mulVec z) := by
  have hA_sub : (Matrix.fromBlocks A C Cᴴ B).submatrix Sum.inl Sum.inl = A := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁]
  have hA_psd : A.PosSemidef := by
    have hsub := h.submatrix (Sum.inl : n → n ⊕ n)
    simpa [Matrix.submatrix_submatrix, Matrix.submatrix_apply, hA_sub] using hsub
  exact hA_psd.dotProduct_mulVec_nonneg z

-- (Uses `dotProduct_star_self_eq_zero` from Mathlib)

omit [DecidableEq n] in
/-- The quadratic form of a `fromBlocks` matrix on a `Sum`-type vector.

For M = [[A, B], [C, D]] and x = (v, w), we have
x† M x = v†A v + v†B w + w†C v + w†D w. -/
private lemma fromBlocks_quadratic_form {A B C D : Mat} (v w : n → ℂ) :
    star (Sum.elim v w) ⬝ᵥ ((Matrix.fromBlocks A B C D).mulVec (Sum.elim v w)) =
    star v ⬝ᵥ (A.mulVec v) + star v ⬝ᵥ (B.mulVec w) +
    star w ⬝ᵥ (C.mulVec v) + star w ⬝ᵥ (D.mulVec w) := by
  calc
    star (Sum.elim v w) ⬝ᵥ ((Matrix.fromBlocks A B C D).mulVec (Sum.elim v w))
        = star (Sum.elim v w) ⬝ᵥ
          (Sum.elim (A.mulVec v + B.mulVec w) (C.mulVec v + D.mulVec w)) := by
      rw [fromBlocks_mulVec (A := A) (B := B) (C := C) (D := D) (x := Sum.elim v w)]
      simp
    _ = star v ⬝ᵥ (A.mulVec v + B.mulVec w) + star w ⬝ᵥ (C.mulVec v + D.mulVec w) := by
      have h_star_elim : star (Sum.elim v w) = Sum.elim (star v) (star w) := by
        ext x; cases x <;> simp
      rw [h_star_elim, sumElim_dotProduct_sumElim]
    _ = (star v ⬝ᵥ (A.mulVec v) + star v ⬝ᵥ (B.mulVec w)) +
        (star w ⬝ᵥ (C.mulVec v) + star w ⬝ᵥ (D.mulVec w)) := by
      simp [dotProduct_add]
    _ = star v ⬝ᵥ (A.mulVec v) + star v ⬝ᵥ (B.mulVec w) +
        star w ⬝ᵥ (C.mulVec v) + star w ⬝ᵥ (D.mulVec w) := by ring

/-! ### Schur complement lemmas (singular-block case) -/

omit [DecidableEq n] in
/-- If the `2×2` block matrix `[[A, C], [C†, B]]` is PSD, then `ker(B) ≤ ker(C)`.

This is the kernel-absorption clause of Wolf's Theorem 5.2 (block matrices
and Schur complements): the kernel of the bottom-right block is contained in
the kernel of the off-diagonal block. It is the Schur-complement fact
underlying the range-inclusion and well-definedness steps of the two-variable
Schwarz inequality. -/
lemma ker_inclusion_of_fromBlocks_posSemidef {A C B : Mat}
    (h : (Matrix.fromBlocks A C Cᴴ B : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosSemidef)
    (y : n → ℂ) (hy : B.mulVec y = 0) : C.mulVec y = 0 := by
  set z := C.mulVec y with hz_def
  by_contra! hz_ne
  have hz_norm_sq_pos : 0 < star z ⬝ᵥ z := by
    have h_nonneg : 0 ≤ star z ⬝ᵥ z := by
      simpa [dotProduct] using Finset.sum_nonneg (fun i _ => star_mul_self_nonneg (z i))
    have h_ne_zero : star z ⬝ᵥ z ≠ 0 := by
      intro hzero
      apply hz_ne
      exact (dotProduct_star_self_eq_zero.mp hzero)
    exact h_nonneg.lt_of_ne h_ne_zero.symm
  have ha_nonneg : 0 ≤ star z ⬝ᵥ (A.mulVec z) :=
    dotProduct_mulVec_nonneg_of_posSemidef_block h z
  have ha_real : (star z ⬝ᵥ (A.mulVec z)).im = 0 :=
    ((Complex.nonneg_iff.mp ha_nonneg).2).symm
  have hb_real : (star z ⬝ᵥ z).im = 0 := by
    dsimp [dotProduct]
    rw [Complex.im_sum]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    simp [mul_comm]
  have hyCz_eq : star y ⬝ᵥ (Cᴴ.mulVec z) = star z ⬝ᵥ z := by
    calc
      star y ⬝ᵥ (Cᴴ.mulVec z) = (star y ᵥ* Cᴴ) ⬝ᵥ z := by rw [dotProduct_mulVec]
      _ = (star (C.mulVec y)) ⬝ᵥ z := by
        have h_vec_eq : (star y ᵥ* Cᴴ) = star (C.mulVec y) := by
          funext j
          simp [Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]
        rw [h_vec_eq]
      _ = star z ⬝ᵥ z := by rw [hz_def]
  -- Quadratic expansion using fromBlocks_quadratic_form
  have h_quad_eq (t : ℝ) : star (Sum.elim ((t : ℂ) • z) y) ⬝ᵥ
      ((Matrix.fromBlocks A C Cᴴ B).mulVec (Sum.elim ((t : ℂ) • z) y)) =
    ((t : ℂ) ^ 2) * (star z ⬝ᵥ (A.mulVec z)) + (2 : ℂ) * (t : ℂ) * (star z ⬝ᵥ z) := by
    rw [fromBlocks_quadratic_form ((t : ℂ) • z) y]
    rw [hy, ← hz_def]
    simp [Matrix.mulVec_smul, dotProduct_smul, star_smul,
      mul_comm, mul_assoc, hyCz_eq, add_comm]
    ring
  have h_quad_nonneg (t : ℝ) : 0 ≤ ((t : ℂ) ^ 2) * (star z ⬝ᵥ (A.mulVec z)) +
      (2 : ℂ) * (t : ℂ) * (star z ⬝ᵥ z) := by
    rw [← h_quad_eq t]
    let x : (n ⊕ n) → ℂ := Sum.elim ((t : ℂ) • z) y
    exact h.dotProduct_mulVec_nonneg x
  have h_quad_real (t : ℝ) : 0 ≤ t ^ 2 * ((star z ⬝ᵥ (A.mulVec z)).re : ℝ) +
      2 * t * ((star z ⬝ᵥ z).re : ℝ) := by
    have h_nonneg := h_quad_nonneg t
    have h_real := (Complex.nonneg_iff.mp h_nonneg).1
    have ha_eq : (star z ⬝ᵥ (A.mulVec z) : ℂ) =
        ((star z ⬝ᵥ (A.mulVec z)).re : ℂ) := by
      calc
        (star z ⬝ᵥ (A.mulVec z) : ℂ) =
            ((star z ⬝ᵥ (A.mulVec z)).re : ℂ) +
            ((star z ⬝ᵥ (A.mulVec z)).im : ℂ) * I := (Complex.re_add_im _).symm
        _ = ((star z ⬝ᵥ (A.mulVec z)).re : ℂ) + (0 : ℂ) * I := by simp [ha_real]
        _ = ((star z ⬝ᵥ (A.mulVec z)).re : ℂ) := by simp
    have hb_eq : (star z ⬝ᵥ z : ℂ) = ((star z ⬝ᵥ z).re : ℂ) := by
      calc
        (star z ⬝ᵥ z : ℂ) = ((star z ⬝ᵥ z).re : ℂ) + ((star z ⬝ᵥ z).im : ℂ) * I :=
          (Complex.re_add_im _).symm
        _ = ((star z ⬝ᵥ z).re : ℂ) + (0 : ℂ) * I := by simp [hb_real]
        _ = ((star z ⬝ᵥ z).re : ℂ) := by simp
    set X : ℝ := t ^ 2 * ((star z ⬝ᵥ (A.mulVec z)).re : ℝ) +
        2 * t * ((star z ⬝ᵥ z).re : ℝ) with hX
    have h_expr_eq : ((t : ℂ) ^ 2) * (star z ⬝ᵥ (A.mulVec z)) +
        (2 : ℂ) * (t : ℂ) * (star z ⬝ᵥ z) = (X : ℂ) := by
      rw [ha_eq, hb_eq]
      dsimp [X]
      push_cast
      ring
    have hexpr : (((t : ℂ) ^ 2) * (star z ⬝ᵥ (A.mulVec z)) +
        (2 : ℂ) * (t : ℂ) * (star z ⬝ᵥ z)).re = X := by
      rw [h_expr_eq]
      simp
    rw [hexpr] at h_real
    exact h_real
  have hb_re_zero : ((star z ⬝ᵥ z).re : ℝ) = 0 := by
    have h_quad' : ∀ t : ℝ, 0 ≤ t * (2 * ((star z ⬝ᵥ z).re : ℝ)) +
      t ^ 2 * ((star z ⬝ᵥ (A.mulVec z)).re : ℝ) := by
      intro t
      -- h_quad_real t gives 0 ≤ t^2*(a.re) + 2*t*(b.re)
      -- which is the same as 0 ≤ t*(2*b.re) + t^2*(a.re)
      simpa [mul_comm, add_comm, mul_left_comm, add_left_comm, mul_assoc] using h_quad_real t
    have h_two_b_zero := SchwarzMap.linear_eq_zero_of_quadratic_nonneg
      (2 * ((star z ⬝ᵥ z).re : ℝ)) ((star z ⬝ᵥ (A.mulVec z)).re : ℝ) h_quad'
    linarith
  have hb_zero : star z ⬝ᵥ z = 0 := by
    calc
      star z ⬝ᵥ z = ((star z ⬝ᵥ z).re : ℂ) + ((star z ⬝ᵥ z).im : ℂ) * I :=
        (Complex.re_add_im _).symm
      _ = ((star z ⬝ᵥ z).re : ℂ) + (0 : ℂ) * I := by simp [hb_real]
      _ = ((star z ⬝ᵥ z).re : ℂ) := by simp
      _ = (0 : ℂ) := by simp [hb_re_zero]
  rw [hb_zero] at hz_norm_sq_pos
  exact lt_irrefl 0 hz_norm_sq_pos

omit [DecidableEq n] in
/-- Schur-complement quadratic-form inequality for a PSD block matrix.

Given a PSD block matrix `[[Amat, Cmat], [CstarMat, Bmat]]` and vectors `v, w`
satisfying `Bmat * w = CstarMat * v`, the quadratic form yields
`v† Amat v ≥ v† Cmat w`.  When the block matrix is Hermitian (as it is when PSD),
`CstarMat = Cmat†` and this specializes to Wolf's Schur complement
characterization (Theorem 5.2). -/
lemma schwarz_inequality_of_fromBlocks_posSemidef {Amat Cmat CstarMat Bmat : Mat}
    (h : (Matrix.fromBlocks Amat Cmat CstarMat Bmat :
      Matrix (n ⊕ n) (n ⊕ n) ℂ).PosSemidef)
    (v w : n → ℂ) (hwB : Bmat.mulVec w = CstarMat.mulVec v) :
    star v ⬝ᵥ (Amat.mulVec v) ≥ star v ⬝ᵥ (Cmat.mulVec w) := by
  let x : (n ⊕ n) → ℂ := Sum.elim v (-w)
  have hx_nonneg := h.dotProduct_mulVec_nonneg x
  dsimp [x] at hx_nonneg
  rw [fromBlocks_mulVec (A := Amat) (B := Cmat)
    (C := CstarMat) (D := Bmat) (x := Sum.elim v (-w))] at hx_nonneg
  -- Now: 0 ≤ star (Sum.elim v (-w)) ⬝ᵥ
  --   Sum.elim (Amat.mulVec v + Cmat.mulVec (-w)) (CstarMat.mulVec v + Bmat.mulVec (-w))
  have h_star_elim : star (Sum.elim v (-w)) = Sum.elim (star v) (star (-w)) := by
    ext i; cases i <;> simp
  rw [h_star_elim] at hx_nonneg
  -- 0 ≤ Sum.elim (star v) (-star w) ⬝ᵥ
  --   Sum.elim (Amat.mulVec v - Cmat.mulVec w) (CstarMat.mulVec v - Bmat.mulVec w)
  rw [sumElim_dotProduct_sumElim] at hx_nonneg
  -- 0 ≤ (star v ⬝ᵥ (Amat.mulVec v - Cmat.mulVec w))
  --   + (-star w ⬝ᵥ (CstarMat.mulVec v - Bmat.mulVec w))
  have hx_nonneg' :
      0 ≤ star v ⬝ᵥ (Amat.mulVec v) + -(star v ⬝ᵥ (Cmat.mulVec w)) +
        (-(star w ⬝ᵥ (CstarMat.mulVec v)) + star w ⬝ᵥ (Bmat.mulVec w)) := by
    simpa [Matrix.mulVec_neg, dotProduct_neg, dotProduct_add] using hx_nonneg
  -- 0 ≤ star v ⬝ᵥ Amat.mulVec v - star v ⬝ᵥ Cmat.mulVec w
  --   - star w ⬝ᵥ CstarMat.mulVec v + star w ⬝ᵥ Bmat.mulVec w
  rw [hwB] at hx_nonneg'
  -- 0 ≤ star v ⬝ᵥ Amat.mulVec v - star v ⬝ᵥ Cmat.mulVec w
  --   - star w ⬝ᵥ CstarMat.mulVec v + star w ⬝ᵥ CstarMat.mulVec v
  ring_nf at hx_nonneg'
  simpa using hx_nonneg'

/-! ### Main theorem -/

omit [DecidableEq n] in
/-- **Two-variable operator Schwarz inequality** (Wolf, Theorem 5.3).

For a 2-positive linear map `E` and all matrices `A, B`, for all vectors `v, w`
with `E(B†B) w = E(B†A) v`, we have `v† E(A†A) v ≥ v† E(A†B) w`.

This is the pseudoinverse-free formulation of Wolf's Eq. (5.4):
`E(A†B) E(B†B)⁻¹ E(B†A) ≤ E(A†A)` where the inverse is taken on the range. -/
theorem schwarz_two_variable (E : Mat →ₗ[ℂ] Mat) (h2pos : Is2PositiveMap E)
    (A B : Mat) (v w : n → ℂ) (hw : (E (Bᴴ * B)).mulVec w = (E (Bᴴ * A)).mulVec v) :
    star v ⬝ᵥ ((E (Aᴴ * A)).mulVec v) ≥ star v ⬝ᵥ ((E (Aᴴ * B)).mulVec w) := by
  have h_block_psd := ampliated_block_matrix_posSemidef E h2pos A B
  exact schwarz_inequality_of_fromBlocks_posSemidef h_block_psd v w hw

end SchwarzTwoVariable

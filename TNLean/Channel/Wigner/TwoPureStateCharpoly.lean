/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import TNLean.Channel.Wigner.ProjectivePureState

/-!
# Characteristic polynomial of two pure states

This module proves the multiplicity-aware form of the two-pure-state spectrum calculation in
Wolf, Chapter 1, lines 289--296. In dimension at least two, the proof factors the sum of the two
pure-state matrices as a rectangular product and compares the characteristic polynomials of the
two product orders. The dimensions zero and one are treated separately.

## Main results

* `Projectivization.charpoly_add_pureStateMatrix_of_two_le`
* `Projectivization.charpoly_add_pureStateMatrix_fin_one`
* `Projectivization.trace_pureStateMatrix_mul_eq_of_charpoly_add_eq`
-/

open scoped LinearAlgebra.Projectivization Matrix
open Polynomial

namespace Projectivization

variable {d : ℕ}

/-- There are no projective rays in the zero-dimensional complex vector space. -/
theorem isEmpty_projectivization_fin_zero : IsEmpty (ℙ ℂ (Fin 0 → ℂ)) := by
  constructor
  intro p
  exact p.rep_nonzero (Subsingleton.elim p.rep 0)

/-- In complex dimension one, every normalized pure-state matrix is the identity. -/
theorem pureStateMatrix_fin_one (p : ℙ ℂ (Fin 1 → ℂ)) : pureStateMatrix p = 1 := by
  have htr := trace_pureStateMatrix p
  ext i j
  fin_cases i
  fin_cases j
  simpa [Matrix.trace_fin_one] using htr

/-- In complex dimension one, the sum of two pure-state matrices has characteristic polynomial
$X-2$. This is the explicit low-dimensional replacement for the formula with exponent $d-2$. -/
theorem charpoly_add_pureStateMatrix_fin_one (p q : ℙ ℂ (Fin 1 → ℂ)) :
    (pureStateMatrix p + pureStateMatrix q).charpoly = X - 2 := by
  rw [pureStateMatrix_fin_one p, pureStateMatrix_fin_one q]
  simp [Matrix.charpoly, Matrix.charmatrix]
  norm_num

private theorem star_dot_self_ne_zero (v : Fin d → ℂ) (hv : v ≠ 0) :
    star v ⬝ᵥ v ≠ 0 := by
  rw [dotProduct_comm]
  let w : EuclideanSpace ℂ (Fin d) := WithLp.toLp 2 v
  have hw : w ≠ 0 := by simpa [w] using hv
  rw [← EuclideanSpace.inner_eq_star_dotProduct w w]
  exact inner_self_ne_zero (𝕜 := ℂ) |>.mpr hw

/-- The multiplicity-aware characteristic polynomial of the sum of two normalized pure-state
matrices in dimension at least two. This is Wolf's Chapter 1 calculation with the omitted
$d-2$ zero eigenvalues restored. -/
theorem charpoly_add_pureStateMatrix_of_two_le (hd : 2 ≤ d)
    (p q : ℙ ℂ (Fin d → ℂ)) :
    (pureStateMatrix p + pureStateMatrix q).charpoly =
      X ^ (d - 2) *
        ((X - 1) ^ 2 - C (Matrix.trace (pureStateMatrix p * pureStateMatrix q))) := by
  classical
  let vp := p.rep
  let vq := q.rep
  let ap : ℂ := star vp ⬝ᵥ vp
  let aq : ℂ := star vq ⬝ᵥ vq
  have hap : ap ≠ 0 := star_dot_self_ne_zero vp p.rep_nonzero
  have haq : aq ≠ 0 := star_dot_self_ne_zero vq q.rep_nonzero
  let A : Matrix (Fin d) (Fin 2) ℂ := fun i j ↦ ![vp i, vq i] j
  let B : Matrix (Fin 2) (Fin d) ℂ :=
    fun j i ↦ ![ap⁻¹ * star (vp i), aq⁻¹ * star (vq i)] j
  have hAB : A * B = pureStateMatrix p + pureStateMatrix q := by
    rw [← p.mk_rep, ← q.mk_rep, pureStateMatrix_mk, pureStateMatrix_mk]
    ext i j
    simp [A, B, Matrix.mul_apply, Fin.sum_univ_two, normalizedPureStateMatrix, vp, vq,
      ap, aq, Matrix.vecMulVec_apply, Pi.star_apply]
    ring
  have h00 : (B * A) 0 0 = 1 := by
    simp only [A, B, Matrix.mul_apply, Matrix.cons_val_zero, ap, vp]
    calc
      ∑ x, ap⁻¹ * star (vp x) * vp x = ap⁻¹ * ∑ x, star (vp x) * vp x := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ap⁻¹ * ap := rfl
      _ = 1 := inv_mul_cancel₀ hap
  have h11 : (B * A) 1 1 = 1 := by
    simp only [A, B, Matrix.mul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, aq, vq]
    calc
      ∑ x, aq⁻¹ * star (vq x) * vq x = aq⁻¹ * ∑ x, star (vq x) * vq x := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = aq⁻¹ * aq := rfl
      _ = 1 := inv_mul_cancel₀ haq
  have h01 : (B * A) 0 1 = ap⁻¹ * (star vp ⬝ᵥ vq) := by
    simp only [A, B, Matrix.mul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, dotProduct,
      Pi.star_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h10 : (B * A) 1 0 = aq⁻¹ * (star vq ⬝ᵥ vp) := by
    simp only [A, B, Matrix.mul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, dotProduct,
      Pi.star_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have htr : (B * A).trace = 2 := by
    rw [Matrix.trace_fin_two, h00, h11]
    norm_num
  have hdet : (B * A).det =
      1 - Matrix.trace (pureStateMatrix p * pureStateMatrix q) := by
    rw [Matrix.det_fin_two, h00, h11, h01, h10,
      trace_pureStateMatrix_mul_pureStateMatrix]
    simp only [transitionProbability, vp, vq, ap, aq]
    field_simp
  rw [← hAB, Matrix.charpoly_mul_comm_of_le A B]
  · rw [Matrix.charpoly_fin_two, htr, hdet]
    simp only [Fintype.card_fin]
    congr 1
    rw [map_sub, map_one, Polynomial.C_ofNat]
    ring
  · simpa using hd

/-- Equality of the characteristic polynomials of two sums of pure-state matrices determines
the transition probability, in every dimension. The zero-dimensional case has no rays, the
one-dimensional case is constant, and dimensions at least two follow by cancelling the restored
factor $X^{d-2}$. -/
theorem trace_pureStateMatrix_mul_eq_of_charpoly_add_eq
    (p q r s : ℙ ℂ (Fin d → ℂ))
    (hchar : (pureStateMatrix p + pureStateMatrix q).charpoly =
      (pureStateMatrix r + pureStateMatrix s).charpoly) :
    Matrix.trace (pureStateMatrix p * pureStateMatrix q) =
      Matrix.trace (pureStateMatrix r * pureStateMatrix s) := by
  by_cases hd0 : d = 0
  · subst d
    exact (isEmpty_projectivization_fin_zero.false p).elim
  by_cases hd1 : d = 1
  · subst d
    simp [pureStateMatrix_fin_one]
  have hd : 2 ≤ d := by omega
  rw [charpoly_add_pureStateMatrix_of_two_le hd,
    charpoly_add_pureStateMatrix_of_two_le hd] at hchar
  have hpow : X ^ (d - 2) ≠ (0 : Polynomial ℂ) :=
    pow_ne_zero _ X_ne_zero
  have hquadratic := mul_left_cancel₀ hpow hchar
  have hconstant :
      C (Matrix.trace (pureStateMatrix p * pureStateMatrix q)) =
        C (Matrix.trace (pureStateMatrix r * pureStateMatrix s)) :=
    sub_right_inj.mp hquadratic
  exact C_injective hconstant

end Projectivization

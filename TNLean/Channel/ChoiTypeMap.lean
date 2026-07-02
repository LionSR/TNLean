/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import TNLean.Algebra.HermitianHelpers

/-!
# Choi-type positive maps

This file records the Choi-type maps appearing in Wolf Chapter 3, Example 3.1,
equation (3.20).  The map is written on the cyclic index set `ZMod d`, which is
the natural home for the shift matrices \(U_{k0}\):
\[
  T_C(X)=(d-n)D(X)-X+\sum_{k=1}^{n}D(U_{k0}XU_{k0}^{\dagger}),
\]
where `D` projects a matrix to its diagonal part.

The main theorem in this file is the exact action on rank-one projectors.  This
is the algebraic reduction needed for the later positivity proof of Wolf
Example 3.1.  Positivity and indecomposability of the Choi-type maps are not
proved here.  The remaining positivity step is a genuine cyclic reciprocal
inequality for the diagonal weights; it does not follow merely from equality
between the total numerator weight and the total denominator weight.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 3,
  Example 3.1, equation (3.20)][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder InnerProductSpace
open Finset

namespace Matrix

variable {d : ℕ} [NeZero d]

/-! ## Basic cyclic and diagonal operations -/

/-- The cyclic shift matrix \(U_{k0}\) from Wolf, equation (2.24), sending
\(\ket r\) to \(\ket{k+r}\). -/
def choiTypeShift (k : ZMod d) : Matrix (ZMod d) (ZMod d) ℂ :=
  (Equiv.addRight (-k)).permMatrix ℂ

/-- The diagonal projection \(D(X)\), which keeps the diagonal entries and
sets all off-diagonal entries to zero. -/
def diagonalProjection (d : ℕ) :
    Matrix (ZMod d) (ZMod d) ℂ →ₗ[ℂ] Matrix (ZMod d) (ZMod d) ℂ where
  toFun X := diagonal fun i => X i i
  map_add' X Y := by
    ext i j
    by_cases h : i = j <;> simp [h]
  map_smul' c X := by
    ext i j
    by_cases h : i = j <;> simp [h]

omit [NeZero d] in
@[simp]
theorem diagonalProjection_apply (X : Matrix (ZMod d) (ZMod d) ℂ) :
    diagonalProjection d X = diagonal fun i => X i i :=
  rfl

/-- Conjugation by a matrix, as the linear map \(X\mapsto AXA^\dagger\).

Wolf's Choi-type maps use this operation in the terms
\(U_{k0}XU_{k0}^{\dagger}\).  As a map on matrices it is completely positive;
that fact is not used in this file. -/
def conjugationLinearMap {n : Type*} [Fintype n]
    (A : Matrix n n ℂ) : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun X := A * X * Aᴴ
  map_add' X Y := by
    simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

@[simp]
theorem conjugationLinearMap_apply {n : Type*} [Fintype n]
    (A : Matrix n n ℂ) (X : Matrix n n ℂ) :
    conjugationLinearMap A X = A * X * Aᴴ :=
  rfl

/-- The diagonal part of a cyclically conjugated matrix is the shifted diagonal. -/
theorem diagonalProjection_conj_choiTypeShift
    (k : ZMod d) (X : Matrix (ZMod d) (ZMod d) ℂ) :
    diagonalProjection d (choiTypeShift k * X * (choiTypeShift k)ᴴ) =
      diagonal fun i => X (i - k) (i - k) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [diagonalProjection, choiTypeShift, Equiv.Perm.permMatrix,
      PEquiv.toMatrix, Matrix.mul_apply, sub_eq_add_neg]
  · simp [diagonalProjection, h]

/-! ## The Choi-type map -/

/-- **Wolf Chapter 3, Example 3.1, equation (3.20).**  The Choi-type map
\[
  T_C(X)=(d-n)D(X)-X+\sum_{k=1}^{n}D(U_{k0}XU_{k0}^{\dagger})
\]
on matrices indexed by the cyclic group `ZMod d`.  The coefficient `d - n` is
the scalar difference appearing in the source; the positivity theorem uses the
range `1 ≤ n ≤ d - 2`. -/
def choiTypeMap (d n : ℕ) [NeZero d] :
    Matrix (ZMod d) (ZMod d) ℂ →ₗ[ℂ] Matrix (ZMod d) (ZMod d) ℂ :=
  ((d : ℂ) - (n : ℂ)) • diagonalProjection d - LinearMap.id +
    ∑ k : Fin n,
      (diagonalProjection d).comp
        (conjugationLinearMap (choiTypeShift ((k.1 + 1 : ℕ) : ZMod d)))

@[simp]
theorem choiTypeMap_apply (n : ℕ) (X : Matrix (ZMod d) (ZMod d) ℂ) :
    choiTypeMap d n X =
      ((d : ℂ) - (n : ℂ)) • diagonalProjection d X - X +
        ∑ k : Fin n,
          diagonalProjection d
            (choiTypeShift ((k.1 + 1 : ℕ) : ZMod d) * X *
              (choiTypeShift ((k.1 + 1 : ℕ) : ZMod d))ᴴ) := by
  simp [choiTypeMap]

/-- The Choi-type map applied to a rank-one projector is a diagonal matrix minus
that projector.  This is the rank-one reduction underlying Wolf's positivity
argument for equation (3.20). -/
theorem choiTypeMap_vecMulVec
    (n : ℕ) (v : ZMod d → ℂ) :
    choiTypeMap d n (vecMulVec v (star v)) =
      diagonal (fun i =>
        ((d : ℂ) - (n : ℂ)) * (v i * star (v i)) +
          ∑ k : Fin n,
            v (i - ((k.1 + 1 : ℕ) : ZMod d)) *
              star (v (i - ((k.1 + 1 : ℕ) : ZMod d)))) -
        vecMulVec v (star v) := by
  rw [choiTypeMap_apply]
  simp_rw [diagonalProjection_conj_choiTypeShift]
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.sum_apply, vecMulVec_apply, smul_eq_mul]
    ring_nf
  · simp [Matrix.sum_apply, vecMulVec_apply, h, smul_eq_mul]

/-- The real diagonal weight appearing in the rank-one Choi-type image. -/
noncomputable def choiTypeRankOneWeight (d n : ℕ) [NeZero d] (v : ZMod d → ℂ)
    (i : ZMod d) : ℝ :=
  ((d : ℝ) - (n : ℝ)) * ‖v i‖ ^ 2 +
    ∑ k : Fin n, ‖v (i - ((k.1 + 1 : ℕ) : ZMod d))‖ ^ 2

/-- Rank-one positivity of the Choi-type map reduced to the cyclic reciprocal
bound for the diagonal weights.

In the range \(n \le d-2\), the remaining scalar task is to prove the displayed
bound for all vectors `v`.  The cyclic placement of the shifted weights is
essential; equality of the two total sums alone does not imply such a bound. -/
theorem choiTypeMap_vecMulVec_posSemidef_of_weight_sum_le_one
    (n : ℕ) (v : ZMod d → ℂ) (hn₂ : n ≤ d - 2)
    (hbound : ∑ i, ‖v i‖ ^ 2 / choiTypeRankOneWeight d n v i ≤ 1) :
    (choiTypeMap d n (vecMulVec v (star v))).PosSemidef := by
  classical
  let a : ZMod d → ℝ := fun i => choiTypeRankOneWeight d n v i
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hnlt : n < d := by omega
  have hnle : n ≤ d := le_of_lt hnlt
  have hdn_nonneg : 0 ≤ (d : ℝ) - (n : ℝ) := by
    have hnleR : (n : ℝ) ≤ (d : ℝ) := by exact_mod_cast hnle
    linarith
  have hdn_pos : 0 < (d : ℝ) - (n : ℝ) := by
    have hnltR : (n : ℝ) < (d : ℝ) := by exact_mod_cast hnlt
    linarith
  have ha : ∀ i, 0 ≤ a i := by
    intro i
    dsimp [a, choiTypeRankOneWeight]
    exact add_nonneg (mul_nonneg hdn_nonneg (sq_nonneg _))
      (Finset.sum_nonneg fun k _ => sq_nonneg _)
  have hvzero : ∀ i, a i = 0 → v i = 0 := by
    intro i hi
    have hfirst_nonneg : 0 ≤ ((d : ℝ) - (n : ℝ)) * ‖v i‖ ^ 2 :=
      mul_nonneg hdn_nonneg (sq_nonneg _)
    have hsum_nonneg :
        0 ≤ ∑ k : Fin n, ‖v (i - ((k.1 + 1 : ℕ) : ZMod d))‖ ^ 2 :=
      Finset.sum_nonneg fun k _ => sq_nonneg _
    have hsum_eq :
        ((d : ℝ) - (n : ℝ)) * ‖v i‖ ^ 2 +
            ∑ k : Fin n, ‖v (i - ((k.1 + 1 : ℕ) : ZMod d))‖ ^ 2 = 0 := by
      simpa [a, choiTypeRankOneWeight] using hi
    have hfirst_zero : ((d : ℝ) - (n : ℝ)) * ‖v i‖ ^ 2 = 0 := by
      nlinarith
    have hnormsq_zero : ‖v i‖ ^ 2 = 0 := by
      nlinarith [hfirst_zero, hdn_pos, sq_nonneg (‖v i‖)]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnormsq_zero)
  have hdiag :
      (diagonal (fun i => (a i : ℂ)) - vecMulVec v (star v)).PosSemidef :=
    diagonal_sub_vecMulVec_posSemidef_of_sum_normSq_div_le_one a v ha hvzero
      (by simpa [a] using hbound)
  rw [choiTypeMap_vecMulVec]
  convert hdiag using 1
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [a, choiTypeRankOneWeight, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  · simp [hij]

end Matrix

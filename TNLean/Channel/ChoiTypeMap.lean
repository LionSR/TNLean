/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation

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
proved here.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 3,
  Example 3.1, equation (3.20)][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder
open Finset

namespace Matrix

variable {d : ℕ} [NeZero d]

/-! ## Basic cyclic and diagonal operations -/

/-- The cyclic shift matrix on `ZMod d`, indexed by addition by `k`. -/
def choiTypeShift (k : ZMod d) : Matrix (ZMod d) (ZMod d) ℂ :=
  (Equiv.addRight k).permMatrix ℂ

/-- The diagonal projection \(D(X)\), which keeps the diagonal entries and
sets all off-diagonal entries to zero. -/
noncomputable def diagonalProjection (d : ℕ) [NeZero d] :
    Matrix (ZMod d) (ZMod d) ℂ →ₗ[ℂ] Matrix (ZMod d) (ZMod d) ℂ where
  toFun X := diagonal fun i => X i i
  map_add' X Y := by
    ext i j
    by_cases h : i = j <;> simp [h]
  map_smul' c X := by
    ext i j
    by_cases h : i = j <;> simp [h]

@[simp]
theorem diagonalProjection_apply (X : Matrix (ZMod d) (ZMod d) ℂ) :
    diagonalProjection d X = diagonal fun i => X i i :=
  rfl

/-- Conjugation by a matrix, as a linear map. -/
noncomputable def conjugationLinearMap {n : Type*} [Fintype n]
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
      diagonal fun i => X (i + k) (i + k) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [diagonalProjection, choiTypeShift, Equiv.Perm.permMatrix,
      PEquiv.toMatrix, Matrix.mul_apply]
  · simp [diagonalProjection, h]

/-! ## The Choi-type map -/

/-- **Wolf Chapter 3, Example 3.1, equation (3.20).**  The Choi-type map
\[
  T_C(X)=(d-n)D(X)-X+\sum_{k=1}^{n}D(U_{k0}XU_{k0}^{\dagger})
\]
on matrices indexed by the cyclic group `ZMod d`.  The coefficient `d - n` is
the scalar difference appearing in the source; the positivity theorem uses the
range `1 ≤ n ≤ d - 2`. -/
noncomputable def choiTypeMap (d n : ℕ) [NeZero d] :
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
            v (i + ((k.1 + 1 : ℕ) : ZMod d)) *
              star (v (i + ((k.1 + 1 : ℕ) : ZMod d)))) -
        vecMulVec v (star v) := by
  rw [choiTypeMap_apply]
  simp_rw [diagonalProjection_conj_choiTypeShift]
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.sum_apply, vecMulVec_apply, smul_eq_mul]
    ring_nf
  · simp [Matrix.sum_apply, vecMulVec_apply, h, smul_eq_mul]

end Matrix

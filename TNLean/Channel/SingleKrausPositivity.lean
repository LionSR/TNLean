/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixUnitaryBetween
import TNLean.Channel.KrausCPTP
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Positivity under single-Kraus isometries

This file records algebraic and order properties of conjugation by a rectangular
isometry.

## Main results

* `Matrix.rank_singleKrausMap_of_mem_unitaryGroup`: unitary single-Kraus
  conjugation preserves rank.
* `Matrix.singleKrausMap_kronecker`: single-Kraus conjugation distributes over
  Kronecker products.
* `Matrix.singleKrausMap_mul_of_isometry`: isometric single-Kraus conjugation
  preserves multiplication.
* `Matrix.singleKrausMap_charpoly_eq_X_pow_mul_of_isometry`: isometric conjugation pads the
  characteristic polynomial by zero roots.
* `Matrix.singleKrausMap_charpoly_roots_eq_zero_add_of_isometry`: the corresponding root-multiset
  identity.
* `Matrix.posSemidef_of_singleKraus_isometry`: positivity can be read back
  through an isometric single-Kraus conjugation.
-/

open scoped Matrix ComplexOrder Kronecker

/-- A unitary single-Kraus conjugation preserves ordinary matrix rank. -/
theorem Matrix.rank_singleKrausMap_of_mem_unitaryGroup
    {n : Type*} [Fintype n] [DecidableEq n]
    (U A : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    (singleKrausMap U A).rank = A.rank := by
  have hUdet : IsUnit U.det := Matrix.UnitaryGroup.det_isUnit ⟨U, hU⟩
  have hUh : Uᴴ ∈ Matrix.unitaryGroup n ℂ := by
    exact ⟨by simpa only [Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose] using hU.2,
      by simpa only [Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose] using hU.1⟩
  have hUhdet : IsUnit Uᴴ.det := Matrix.UnitaryGroup.det_isUnit ⟨Uᴴ, hUh⟩
  rw [singleKrausMap_apply,
    Matrix.rank_mul_eq_left_of_isUnit_det Uᴴ (U * A) hUhdet,
    Matrix.rank_mul_eq_right_of_isUnit_det U A hUdet]

/-- Single-Kraus conjugation distributes over Kronecker products. -/
theorem Matrix.singleKrausMap_kronecker
    {a b c f : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype f]
    (A : Matrix a b ℂ) (C : Matrix c f ℂ)
    (X : Matrix b b ℂ) (Y : Matrix f f ℂ) :
    singleKrausMap (A ⊗ₖ C) (X ⊗ₖ Y) =
      singleKrausMap A X ⊗ₖ singleKrausMap C Y := by
  simp only [singleKrausMap_apply, Matrix.conjTranspose_kronecker]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]

/-- Single-Kraus conjugation by an isometry preserves multiplication. -/
theorem Matrix.singleKrausMap_mul_of_isometry
    {a b : Type*} [Fintype a] [Fintype b] [DecidableEq b]
    (V : Matrix a b ℂ) (hV : Vᴴ * V = 1)
    (X Y : Matrix b b ℂ) :
    singleKrausMap V (X * Y) =
      singleKrausMap V X * singleKrausMap V Y := by
  simp only [singleKrausMap_apply, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Vᴴ V, hV]
  simp

/-- Isometric single-Kraus conjugation pads the characteristic polynomial by zero roots whose
multiplicity is the codimension of the isometric inclusion. -/
theorem Matrix.singleKrausMap_charpoly_eq_X_pow_mul_of_isometry
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (V : Matrix β α ℂ) (hV : Vᴴ * V = 1) (A : Matrix α α ℂ) :
    (singleKrausMap V A).charpoly =
      Polynomial.X ^ (Fintype.card β - Fintype.card α) * A.charpoly := by
  rw [singleKrausMap_apply, Matrix.mul_assoc,
    Matrix.charpoly_mul_comm_of_le V (A * Vᴴ) (Matrix.IsIsometry.card_le V hV),
    Matrix.mul_assoc, hV, Matrix.mul_one]

/-- The roots after isometric single-Kraus conjugation are the original roots together with one
zero for every dimension added by the isometric inclusion. -/
theorem Matrix.singleKrausMap_charpoly_roots_eq_zero_add_of_isometry
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (V : Matrix β α ℂ) (hV : Vᴴ * V = 1) (A : Matrix α α ℂ) :
    (singleKrausMap V A).charpoly.roots =
      (Fintype.card β - Fintype.card α) • {(0 : ℂ)} + A.charpoly.roots := by
  rw [Matrix.singleKrausMap_charpoly_eq_X_pow_mul_of_isometry V hV A,
    Polynomial.roots_mul, Polynomial.roots_X_pow]
  exact mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (Matrix.charpoly_monic A).ne_zero

/-- Positivity can be read back through an isometric single-Kraus
conjugation. -/
theorem Matrix.posSemidef_of_singleKraus_isometry
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β]
    (V : Matrix β α ℂ) (hV : Vᴴ * V = 1) {X : Matrix α α ℂ}
    (hX : (singleKrausMap V X).PosSemidef) : X.PosSemidef := by
  classical
  have hback := hX.mul_mul_conjTranspose_same Vᴴ
  simp only [singleKrausMap_apply,
    Matrix.conjTranspose_conjTranspose] at hback
  have heq : Vᴴ * (V * X * Vᴴ) * V = X := by
    calc
      _ = (Vᴴ * V) * X * (Vᴴ * V) := by
        simp only [← Matrix.mul_assoc]
      _ = X := by rw [hV, Matrix.one_mul, Matrix.mul_one]
  rw [heq] at hback
  exact hback

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.KrausCPTP
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Positivity under single-Kraus isometries

This file records algebraic and order properties of conjugation by a rectangular
isometry.

## Main declarations

* `Matrix.rank_singleKrausMap_of_mem_unitaryGroup`: unitary single-Kraus
  conjugation preserves rank.
* `Matrix.singleKrausMap_kronecker`: single-Kraus conjugation distributes over
  Kronecker products.
* `Matrix.singleKrausMap_mul_of_isometry`: isometric single-Kraus conjugation
  preserves multiplication.
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

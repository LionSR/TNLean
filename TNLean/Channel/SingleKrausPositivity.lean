/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.KrausCPTP

/-!
# Positivity under single-Kraus isometries

This file records the order-reflection property of conjugation by a rectangular
isometry.

## Main declarations

* `Matrix.posSemidef_of_singleKraus_isometry`: positivity can be read back
  through an isometric single-Kraus conjugation.
-/

open scoped Matrix ComplexOrder

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

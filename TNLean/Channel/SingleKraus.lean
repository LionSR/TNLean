/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.KrausCPTP

/-!
# Single-Kraus map identities

This file records composition and trace-adjoint identities for maps given by
conjugation with one rectangular Kraus matrix.

## Main declarations

* `singleKrausMap_comp`: composition corresponds to multiplication of Kraus matrices.
* `Matrix.traceAdjointMap_singleKrausMap`: the trace adjoint corresponds to conjugate
  transposition of the Kraus matrix.
-/

open scoped Matrix

/-- Composition of two single-Kraus maps is the single-Kraus map associated
with the product of their Kraus matrices. -/
theorem singleKrausMap_comp
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (V : Matrix γ β ℂ) (W : Matrix β α ℂ) :
    (singleKrausMap V).comp (singleKrausMap W) =
      singleKrausMap (V * W) := by
  apply LinearMap.ext
  intro X
  simp only [LinearMap.comp_apply, singleKrausMap_apply,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- The trace-pairing adjoint of a single-Kraus map is the single-Kraus map
associated with the conjugate-transposed Kraus matrix. -/
theorem Matrix.traceAdjointMap_singleKrausMap
    {α β : Type*} [Fintype α] [Fintype β]
    (V : Matrix β α ℂ) :
    Matrix.traceAdjointMap (singleKrausMap V) = singleKrausMap Vᴴ := by
  apply LinearMap.ext
  intro X
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro Y
  rw [Matrix.trace_traceAdjointMap_mul]
  simp only [singleKrausMap_apply, Matrix.conjTranspose_conjTranspose]
  calc
    Matrix.trace (X * (V * Y * Vᴴ)) =
        Matrix.trace ((V * Y * Vᴴ) * X) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (Vᴴ * X * (V * Y)) := by
      symm
      exact Matrix.trace_mul_cycle Vᴴ X (V * Y)
    _ = Matrix.trace ((Vᴴ * X * V) * Y) := by
      rw [← Matrix.mul_assoc]

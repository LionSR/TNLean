/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Basic

/-!
# The two-outcome measurement of an orthogonal projector

An orthogonal projector and its complement form a complete positive projection
family. This finite-dimensional identity is used for the charge detection and
interference measurements in SCP10, arXiv:1001.3807, lines 2464–2486 and 2605–2615.
-/

open scoped BigOperators Matrix ComplexOrder
namespace Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An orthogonal projector and its complement are a complete positive binary
measurement. Source: SCP10, the interference measurement, lines 2605–2615;
auxiliary finite-dimensional identity. -/
theorem binaryProjectionFamily_complete (D : Matrix ι ι ℂ)
    (hDh : D.IsHermitian) (hDI : D * D = D) :
    let Q : Bool → Matrix ι ι ℂ := fun b => if b then D else 1 - D
    (∀ b, (Q b).IsHermitian ∧ (Q b).PosSemidef) ∧
    (∀ b c, Q b * Q c = if b = c then Q b else 0) ∧
    (∑ b, Q b) = 1 := by
  let Q : Bool → Matrix ι ι ℂ := fun b => if b then D else 1 - D
  have hCh : (1 - D).IsHermitian := Matrix.isHermitian_one.sub hDh
  have hCI : (1 - D) * (1 - D) = 1 - D := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one,
      hDI, sub_self, sub_zero]
  refine ⟨?_, ?_, ?_⟩
  · intro b
    cases b
    · change (1 - D).IsHermitian ∧ (1 - D).PosSemidef
      refine ⟨hCh, ?_⟩
      have hp := Matrix.posSemidef_self_mul_conjTranspose (1 - D)
      rw [hCh.eq, hCI] at hp
      exact hp
    · change D.IsHermitian ∧ D.PosSemidef
      refine ⟨hDh, ?_⟩
      have hp := Matrix.posSemidef_self_mul_conjTranspose D
      rw [hDh.eq, hDI] at hp
      exact hp
  · intro b c
    cases b <;> cases c <;>
      simp [Matrix.sub_mul, Matrix.mul_sub, hDI]
  · simp

end Matrix

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Algebra.HermitianHelpers
import TNLean.Channel.Basic

/-!
# Examples of positive maps

This file records elementary positive maps from Wolf Chapter 3.

## Main declarations

* `Matrix.reductionMap`: the reduction map
  \(X \mapsto \operatorname{tr}(X) I - k^{-1}X\).
* `Matrix.reductionMap_one_isPositiveMap`: the case \(k=1\) is positive.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 3,
  Example 3.1][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

namespace Matrix

/-- **Wolf Chapter 3, Example 3.1.** The reduction map
\(T_k(X)=\operatorname{tr}(X)I-k^{-1}X\) on \(M_D(\mathbb C)\). -/
noncomputable def reductionMap (D k : ℕ) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ where
  toFun X := Matrix.trace X • (1 : Matrix (Fin D) (Fin D) ℂ) - ((k : ℂ)⁻¹) • X
  map_add' := by
    intro X Y
    ext i j
    simp [Matrix.trace_add, add_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  map_smul' := by
    intro c X
    ext i j
    simp [Matrix.trace_smul, smul_smul, mul_comm, mul_left_comm, mul_assoc]
    ring

@[simp]
theorem reductionMap_apply (D k : ℕ) (X : Matrix (Fin D) (Fin D) ℂ) :
    reductionMap D k X =
      Matrix.trace X • (1 : Matrix (Fin D) (Fin D) ℂ) - ((k : ℂ)⁻¹) • X :=
  rfl

/-- The reduction map \(T_1(X)=\operatorname{tr}(X)I-X\) is positive. -/
theorem reductionMap_one_isPositiveMap {D : ℕ} [NeZero D] :
    IsPositiveMap (reductionMap D 1) := by
  haveI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero (NeZero.ne D))
  intro X hX
  simpa [reductionMap] using
    (Matrix.PosSemidef.trace_smul_one_sub_self_posSemidef hX)

end Matrix

/-
Copyright (c) 2025 MPSLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MPSLean.Spectral.MixedTransfer

import Mathlib.Data.Matrix.Bilinear

/-!
# Rectangular mixed transfer operator

This module generalizes `MPSTensor.mixedTransferMap` to the **rectangular** (heterogeneous bond
dimension) setting.

Given tensors `A : MPSTensor d D₁` and `B : MPSTensor d D₂`, the rectangular mixed transfer map is

$$F_{AB}(X) = \sum_i A^i\, X\, (B^i)^\dagger,$$

acting on matrices `X : Matrix (Fin D₁) (Fin D₂) ℂ`.

The main result is the word-sum expansion for powers of this map,
`mixedTransferMap₂_pow_apply`.
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPSTensor

variable {d D₁ D₂ : ℕ}

section MixedTransferRect

/-- The **rectangular mixed transfer operator** for two tensors `A : MPSTensor d D₁` and
`B : MPSTensor d D₂`.

It acts on `D₁ × D₂` matrices by
`X ↦ ∑ i, A i * X * (B i)ᴴ`.

We implement it using `mulLeftLinearMap` / `mulRightLinearMap` from
`Mathlib.Data.Matrix.Bilinear` (these support heterogeneous matrix multiplication). -/
noncomputable def mixedTransferMap₂ {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) :
    Matrix (Fin D₁) (Fin D₂) ℂ →ₗ[ℂ] Matrix (Fin D₁) (Fin D₂) ℂ :=
  ∑ i : Fin d,
    (mulLeftLinearMap (n := Fin D₂) ℂ (A i)).comp
      (mulRightLinearMap (l := Fin D₁) ℂ ((B i)ᴴ))

/-- Explicit formula for the rectangular mixed transfer operator. -/
@[simp]
lemma mixedTransferMap₂_apply {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (X : Matrix (Fin D₁) (Fin D₂) ℂ) :
    mixedTransferMap₂ A B X = ∑ i : Fin d, A i * X * (B i)ᴴ := by
  classical
  simp [mixedTransferMap₂, Matrix.mul_assoc]

end MixedTransferRect

section IteratedTransfer

/-- Iterating the rectangular mixed transfer map gives a sum over words.

This is the rectangular analogue of `mixedTransferMap_pow_apply`. -/
theorem mixedTransferMap₂_pow_apply {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) (N : ℕ) :
    ∀ X : Matrix (Fin D₁) (Fin D₂) ℂ,
      ((mixedTransferMap₂ A B) ^ N) X =
        ∑ σ : Fin N → Fin d,
          evalWord A (List.ofFn σ) * X * (evalWord B (List.ofFn σ))ᴴ := by
  classical
  induction N with
  | zero =>
      intro X
      simp [evalWord, Finset.univ_unique]
  | succ n ih =>
      intro X
      rw [pow_succ']
      change mixedTransferMap₂ A B (((mixedTransferMap₂ A B) ^ n) X) = _
      rw [ih]
      -- Push `mixedTransferMap₂` through the σ-sum, then expand the definition.
      simp only [map_sum, mixedTransferMap₂_apply]
      -- Reindex words of length `n+1` by head+tail.
      rw [Finset.sum_comm, sum_fin_succ_eq]
      -- Now it suffices to show the summand matches the recursive word evaluation.
      congr 1
      funext i
      apply Finset.sum_congr rfl
      intro τ _
      simp [evalWord, Matrix.conjTranspose_mul, Matrix.mul_assoc]

end IteratedTransfer

end MPSTensor

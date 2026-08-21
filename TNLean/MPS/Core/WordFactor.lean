/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.MPS.Defs

/-!
# Word-factor identities for matrix product tensors

This file records the elementary extension of a one-letter matrix-factor identity
to a nonempty physical word.
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- Letter compatibility extends to every nonempty word. The left and right
matrix families may be indexed by an arbitrary type. -/
theorem exists_evalWord_factor_of_letter_compatibility
    {A : MPSTensor d D} {α : Type*} {F Z : α → Matrix (Fin D) (Fin D) ℂ}
    (hCompat : ∀ i : Fin d, ∃ Y : Matrix (Fin D) (Fin D) ℂ,
      ∀ a : α, Z a * A i = F a * Y)
    (w : List (Fin d)) (hw : w ≠ []) :
    ∃ Y : Matrix (Fin D) (Fin D) ℂ,
      ∀ a : α, Z a * evalWord A w = F a * Y := by
  cases w with
  | nil => cases hw rfl
  | cons i w =>
      obtain ⟨Y, hY⟩ := hCompat i
      refine ⟨Y * evalWord A w, ?_⟩
      intro a
      calc
        Z a * evalWord A (i :: w)
            = Z a * (A i * evalWord A w) := by simp [evalWord]
        _ = (Z a * A i) * evalWord A w := by rw [Matrix.mul_assoc]
        _ = (F a * Y) * evalWord A w := by rw [hY a]
        _ = F a * (Y * evalWord A w) := by rw [Matrix.mul_assoc]

end MPSTensor

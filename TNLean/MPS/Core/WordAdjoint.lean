/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.Word

/-!
# Adjoint of a matrix word

Conjugate transposition reverses the order of a matrix word.  This file records
that identity for the finite matrix families used by matrix product tensors.
-/

open scoped Matrix

namespace Kraus

variable {d D : ℕ}

/-- Conjugate transposition reverses an evaluated matrix word and conjugate-transposes
each letter. -/
theorem evalWord_conjTranspose (A : Fin d → Matrix (Fin D) (Fin D) ℂ) :
    ∀ w : List (Fin d),
      (evalWord A w)ᴴ = evalWord (fun i => (A i)ᴴ) w.reverse := by
  intro w
  induction w with
  | nil =>
      simp [evalWord]
  | cons i w ih =>
      simp [evalWord, Matrix.conjTranspose_mul, ih, evalWord_append,
        List.reverse_cons]

end Kraus

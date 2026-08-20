/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.Matrix.Mul
import TNLean.Kraus.Injectivity

/-!
# Transposition of words in finite matrix families

This module records the elementary relation between transposition and reversal of a matrix word.
It is shared by the rectangular-span and rank-one constructions in the Quantum Wielandt argument.
-/

open scoped Matrix

namespace List

/-- Reversing `List.ofFn` precomposes the indexing function with `Fin.rev`. -/
theorem ofFn_reverse {n : ℕ} {α : Type*} (f : Fin n → α) :
    (List.ofFn f).reverse = List.ofFn (f ∘ Fin.rev) := by
  calc
    (List.ofFn f).reverse = (List.map f (List.finRange n)).reverse := by
      simp only [List.ofFn_eq_map]
    _ = List.map f (List.finRange n).reverse := by simp only [List.map_reverse]
    _ = List.map f (List.map Fin.rev (List.finRange n)) := by
      simp only [List.finRange_reverse]
    _ = List.map (f ∘ Fin.rev) (List.finRange n) := by simp only [List.map_map]
    _ = List.ofFn (f ∘ Fin.rev) := by simp only [List.ofFn_eq_map]

end List

namespace Kraus

variable {d D : ℕ}

/-- Transposing a word product reverses the word. -/
theorem evalWord_transpose
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) :
    ∀ w : List (Fin d),
      (MPSTensor.evalWord K w)ᵀ =
        MPSTensor.evalWord (fun i ↦ (K i)ᵀ) w.reverse := by
  intro w
  induction w with
  | nil => simp [MPSTensor.evalWord]
  | cons i w ih =>
      simp [MPSTensor.evalWord, Matrix.transpose_mul, ih, MPSTensor.evalWord_append]

end Kraus

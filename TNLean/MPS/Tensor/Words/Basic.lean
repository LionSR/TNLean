/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.Word
import Mathlib.LinearAlgebra.Matrix.Reindex
import TNLean.MPS.Tensor.Defs
import TNLean.MPS.Tensor.Physical.Blocking

/-!
# Word evaluation under a reindexing of the bond

Word evaluation of a matrix product tensor commutes with reindexing the bond along an
equivalence.

## Repeated words

`evalWord_replicate`, the elementary identity for evaluating a tensor on a
`List.replicate`-built word, now lives in `TNLean/Kraus/Blocking.lean`,
alongside the rest of the physical-blocking
word-evaluation layer. This file keeps the one matrix-product-vector
consequence, `mpv_const_eq_trace_pow`, which packages that identity as an
`mpv` statement.

## Word-factor identities for matrix product tensors

This file records the elementary extension of a one-letter matrix-factor identity
to a nonempty physical word.

## Moving a scalar grading through a matrix word
-/

open MPTensor

section

open scoped Matrix

namespace MPSTensor

/-- Matrix product tensor word evaluation commutes with reindexing along an equivalence. -/
lemma evalWord_reindex {d D : ℕ} {m : Type*} [Fintype m] [DecidableEq m]
    (e : m ≃ Fin D) (A : Fin d → Matrix m m ℂ) :
    ∀ w : List (Fin d),
      Kraus.evalWord (fun i => (Matrix.reindex e e) (A i)) w =
        (Matrix.reindex e e) (Kraus.evalWord A w) := by
  classical
  intro w; induction w with
  | nil => simp [Kraus.evalWord]
  | cons _ _ ih =>
      simp only [Kraus.evalWord, ih]
      simp [Matrix.submatrix_mul_equiv]

end MPSTensor

end

section

open scoped Matrix
open Kraus (evalWord_replicate)

namespace MPSTensor

variable {d D : ℕ}

/-- The MPV of a constant configuration is the trace of a matrix power. -/
lemma mpv_const_eq_trace_pow (A : MPSTensor d D) (i : Fin d) (L : ℕ) :
    mpv A (fun _ : Fin L => i) = Matrix.trace ((A i) ^ L) := by
  simp only [mpv, coeff, List.ofFn_const, evalWord_replicate]

end MPSTensor

end

section

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
      ∀ a : α, Z a * Kraus.evalWord A w = F a * Y := by
  cases w with
  | nil => cases hw rfl
  | cons i w =>
      obtain ⟨Y, hY⟩ := hCompat i
      refine ⟨Y * Kraus.evalWord A w, ?_⟩
      intro a
      calc
        Z a * Kraus.evalWord A (i :: w)
            = Z a * (A i * Kraus.evalWord A w) := by simp [Kraus.evalWord]
        _ = (Z a * A i) * Kraus.evalWord A w := by rw [Matrix.mul_assoc]
        _ = (F a * Y) * Kraus.evalWord A w := by rw [hY a]
        _ = F a * (Y * Kraus.evalWord A w) := by rw [Matrix.mul_assoc]

end MPSTensor

end

section

namespace MPSTensor

/-- A letter-dependent scalar grading accumulates the product of its scalars along a word. -/
theorem mul_evalWord_of_mul_eq_smul_letter {d D : ℕ} (A : MPSTensor d D)
    (G : Matrix (Fin D) (Fin D) ℂ) (c : Fin d → ℂ)
    (hG : ∀ i, G * A i = c i • (A i * G)) :
    ∀ w : List (Fin d),
      G * Kraus.evalWord A w = (w.map c).prod • (Kraus.evalWord A w * G)
  | [] => by simp
  | i :: w => by
      rw [Kraus.evalWord_cons, ← Matrix.mul_assoc, hG, Matrix.smul_mul, Matrix.mul_assoc,
        mul_evalWord_of_mul_eq_smul_letter A G c hG w, Matrix.mul_smul, smul_smul,
        ← Matrix.mul_assoc, List.map_cons, List.prod_cons]

end MPSTensor

end

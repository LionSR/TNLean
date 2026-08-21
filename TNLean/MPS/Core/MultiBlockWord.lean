/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.MultiBlockWord
import QICLean.MPS.Core.Word

import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Word evaluation over arbitrary finite index types for matrix product tensors

The generic word evaluation on matrices indexed by an arbitrary finite type agrees with
matrix product tensor word evaluation on `Fin` indices. It also commutes with reindexing
along an equivalence.
-/

open scoped Matrix

namespace MPSTensor

/-- On `Fin D` indices, the auxiliary word evaluation agrees with matrix product tensor
word evaluation. -/
@[simp] lemma evalWord_aux_eq {d D : ℕ} (A : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (w : List (Fin d)) :
    _root_.evalWord A w = Kraus.evalWord A w := by
  induction w with
  | nil => simp [Kraus.evalWord, _root_.evalWord]
  | cons i w ih => simp [Kraus.evalWord, _root_.evalWord, ih]

/-- Matrix product tensor word evaluation commutes with reindexing along an equivalence. -/
lemma evalWord_reindex {d D : ℕ} {m : Type*} [Fintype m] [DecidableEq m]
    (e : m ≃ Fin D) (A : Fin d → Matrix m m ℂ) :
    ∀ w : List (Fin d),
      Kraus.evalWord (fun i => (Matrix.reindex e e) (A i)) w =
        (Matrix.reindex e e) (_root_.evalWord A w) := by
  classical
  intro w; induction w with
  | nil => simp [Kraus.evalWord, _root_.evalWord]
  | cons _ _ ih =>
      simp only [Kraus.evalWord, _root_.evalWord, ih]
      simp [Matrix.submatrix_mul_equiv]

end MPSTensor

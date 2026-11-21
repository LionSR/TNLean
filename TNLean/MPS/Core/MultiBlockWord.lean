/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.MultiBlockWord
import QICLean.Kraus.Word

import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Word evaluation under a reindexing of the bond

Word evaluation of a matrix product tensor commutes with reindexing the bond along an
equivalence.
-/

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

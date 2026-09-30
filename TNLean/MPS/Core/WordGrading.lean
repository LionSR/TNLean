/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Defs

/-! # Moving a scalar grading through a matrix word -/

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

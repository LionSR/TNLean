/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.CyclicWielandt.Matrix
import QICLean.Kraus.WordSpan
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Exact word normal form for the cyclic Wielandt example

Every nonzero word containing the jump matrix reduces to `S^k R S^l`,
where `k,l<D`. Its exact length is `1+k+l+n(D-1)+mD`: return blocks
contribute `D-1` letters and full turns contribute `D` letters.
This is the constraint in arXiv:0909.5347, source lines 697–700.
-/

noncomputable section

open scoped Matrix

namespace MPSTensor.CyclicWielandt

variable {D : ℕ} [NeZero D]

/-- Every word has the exact-length normal form used in the cyclic example.
Source: arXiv:0909.5347, source lines 697–700. The disjunction includes the
zero product and the pure-shift word, rather than imposing a nonzero-product
hypothesis on the source family. -/
theorem evalWord_normalForm (hD : 2 ≤ D) (w : List (Fin 2)) :
    Kraus.evalWord (tensor D) w = 0 ∨
      Kraus.evalWord (tensor D) w = shift D ^ w.length ∨
      ∃ k l n m : ℕ, k < D ∧ l < D ∧
        w.length = 1 + k + l + n * (D - 1) + m * D ∧
        Kraus.evalWord (tensor D) w = shift D ^ k * jump D * shift D ^ l := by
  have hdim : D - 1 + 1 = D := by omega
  have hdim2 : D - 2 + 2 = D := by omega
  induction w with
  | nil => exact Or.inr (Or.inl (by simp))
  | cons a w ih =>
      fin_cases a
      · rcases ih with hz | hp | ⟨k, l, n, m, hk, hl, hlen, hmat⟩
        · exact Or.inl (by simp [hz])
        · exact Or.inr (Or.inl (by simp [hp, pow_succ']))
        · right; right
          by_cases hcarry : k + 1 < D
          · refine ⟨k + 1, l, n, m, hcarry, hl, ?_, ?_⟩
            · simp only [List.length_cons]
              omega
            · simp only [Kraus.evalWord_cons, tensor, Matrix.cons_val_zero', hmat,
                ← Matrix.mul_assoc, pow_succ']
          · have hk1 : k + 1 = D := by omega
            refine ⟨0, l, n, m + 1, by omega, hl, ?_, ?_⟩
            · simp only [List.length_cons]
              nlinarith
            · simp only [Kraus.evalWord_cons, tensor, Matrix.cons_val_zero', hmat,
                ← Matrix.mul_assoc, ← pow_succ', hk1, shift_pow_dim,
                pow_zero, one_mul]
      · rcases ih with hz | hp | ⟨k, l, n, m, hk, hl, hlen, hmat⟩
        · exact Or.inl (by simp [hz])
        · right; right
          refine ⟨0, w.length % D, 0, w.length / D,
            by omega, Nat.mod_lt _ (NeZero.pos D), ?_, ?_⟩
          · simp only [List.length_cons, zero_mul, add_zero]
            have hdiv := Nat.mod_add_div w.length D
            nlinarith
          · simp only [Kraus.evalWord_cons, tensor, Matrix.cons_val_succ', Matrix.cons_val_zero', hp, pow_zero, one_mul]
            rw [shift_pow_mod]
        · by_cases hreturn : k = D - 2
          · right; right
            refine ⟨0, l, n + 1, m, by omega, hl, ?_, ?_⟩
            · simp only [List.length_cons]
              nlinarith
            · simp only [Kraus.evalWord_cons, tensor, Matrix.cons_val_succ', Matrix.cons_val_zero', hmat,
                ← Matrix.mul_assoc, jump_shift_pow_jump hD k hk,
                ite_eq_left hreturn, pow_zero, one_mul]
          · left
            simp only [Kraus.evalWord_cons, tensor, Matrix.cons_val_succ', Matrix.cons_val_zero', hmat,
              ← Matrix.mul_assoc, jump_shift_pow_jump hD k hk,
              ite_eq_right hreturn, zero_mul]

end MPSTensor.CyclicWielandt

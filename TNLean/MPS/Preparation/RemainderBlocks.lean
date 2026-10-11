/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

/-!
# Remainder-absorbing blocks

Partition a positive ring into blocks of length `q`, with the remainder absorbed into the
last block, as in arXiv:2307.01696, Supplemental Material, proof of Theorem 1.

## References

* [arXiv:2307.01696](https://arxiv.org/abs/2307.01696), Supplemental Material, proof of Theorem 1.
-/

open scoped BigOperators

namespace MPSPreparation

/-- Absorb the remainder into the final block, as in arXiv:2307.01696,
Supplemental Material, proof of Theorem 1. -/
def remainderBlockLengths (q N : ℕ) (k : Fin (N / q)) : ℕ :=
  if k.val + 1 = N / q then q + N % q else q

/-- The remainder-absorbing blocks partition the chain whenever `0 < q ≤ N`.
Source: arXiv:2307.01696, Supplemental Material, proof of Theorem 1. -/
theorem sum_remainderBlockLengths {q N : ℕ} (hq : 0 < q) (hqN : q ≤ N) :
    ∑ k, remainderBlockLengths q N k = N := by
  obtain ⟨m, hm⟩ : ∃ m, N / q = m + 1 :=
    ⟨N / q - 1, (Nat.succ_pred_eq_of_pos (Nat.div_pos hqN hq)).symm⟩
  unfold remainderBlockLengths
  rw [hm, Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  have hcast : ∀ k : Fin m, ¬k.val + 1 = m + 1 := fun k => by omega
  simp only [hcast, ite_false, ite_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  have := Nat.div_add_mod N q
  rw [hm] at this
  nlinarith

/-- Each remainder-absorbing block has at least the prescribed number of sites. -/
theorem le_remainderBlockLengths (q N : ℕ) (j : Fin (N / q)) :
    q ≤ remainderBlockLengths q N j := by
  unfold remainderBlockLengths
  split_ifs <;> omega

/-- A positive blocking scale makes every remainder-absorbing block shorter than twice
that scale. -/
theorem remainderBlockLengths_lt_two_mul {q N : ℕ} (hq : 0 < q) (j : Fin (N / q)) :
    remainderBlockLengths q N j < 2 * q := by
  have := Nat.mod_lt N hq
  unfold remainderBlockLengths
  split_ifs <;> omega

/-- For `0 < q ≤ N`, a chain of `N` sites splits into `N / q = m + 1` consecutive blocks whose
lengths lie between `q` and `2 q`: `m` blocks of length `q` and a final block of length
`q + N % q` absorbing the remainder. Source: arXiv:2307.01696, Supplemental Material, proof of
Theorem 1. -/
theorem exists_remainderBlocks {q N : ℕ} (hq : 0 < q) (hqN : q ≤ N) :
    ∃ (m : ℕ) (ℓ : Fin (m + 1) → ℕ), N / q = m + 1 ∧ ∑ k, ℓ k = N ∧
      (∀ k, q ≤ ℓ k) ∧ ∀ k, ℓ k ≤ 2 * q := by
  obtain ⟨m, hm⟩ : ∃ m, N / q = m + 1 :=
    ⟨N / q - 1, (Nat.succ_pred_eq_of_pos (Nat.div_pos hqN hq)).symm⟩
  refine ⟨m, fun k => if k = Fin.last m then q + N % q else q, hm, ?_, fun k => ?_, fun k => ?_⟩
  · rw [Fin.sum_univ_castSucc]
    simp only [Fin.castSucc_ne_last, ite_false, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, ite_true]
    have := Nat.div_add_mod N q
    rw [hm] at this
    linarith
  · dsimp only
    split_ifs <;> omega
  · have := Nat.mod_lt N hq
    dsimp only
    split_ifs <;> omega

end MPSPreparation

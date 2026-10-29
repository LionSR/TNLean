/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.CyclicWielandt.Matrix
import TNLean.Algebra.MatrixSingleSpan
import QICLean.Kraus.Wielandt.RectangularSpan.UniversalityAux.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# Full word span at the cyclic Wielandt length

Return blocks and full turns place every matrix unit except `E₀₀` in
the exact word span at length `D(D-1)`. The pure shift word gives the
identity, and subtracting the other diagonal units gives `E₀₀`.

**Local fix:** The final sentence of the proof in arXiv:0909.5347,
source `main.tex`, lines 697–700, overlooks the pair `k=l=D-1`, whose
length cannot be padded to `D(D-1)`. The identity word supplies this
missing matrix unit. The theorem and dimension range are unchanged;
see `docs/paper-gaps/spwc10_cyclic_missing_diagonal.tex`.
-/

noncomputable section

open scoped Matrix BigOperators Fin.NatCast

namespace MPSTensor.CyclicWielandt

variable {D : ℕ} [NeZero D]

private theorem mul_mem {p q : ℕ} {X Y : Matrix (Fin D) (Fin D) ℂ}
    (hX : X ∈ Kraus.wordSpan (tensor D) p)
    (hY : Y ∈ Kraus.wordSpan (tensor D) q) :
    X * Y ∈ Kraus.wordSpan (tensor D) (p + q) := by
  rw [Kraus.wordSpan_add]
  exact Submodule.mul_mem_mul hX hY

private theorem shift_pow_mem (n : ℕ) :
    shift D ^ n ∈ Kraus.wordSpan (tensor D) n := by
  simpa using Kraus.pow_mem_wordSpan' (tensor D) 0 n

/-- Return blocks realize the same jump at longer exact lengths.
Source: arXiv:0909.5347, source lines 697–700. -/
theorem jump_mem_wordSpan (hD : 2 ≤ D) (n : ℕ) :
    jump D ∈ Kraus.wordSpan (tensor D) (1 + n * (D - 1)) := by
  have hstep : D - 2 + 1 = D - 1 := by omega
  induction n with
  | zero => simpa using Kraus.pow_mem_wordSpan' (tensor D) 1 1
  | succ n ih =>
      have hm := mul_mem (mul_mem ih (shift_pow_mem (D - 2)))
        (show jump D ∈ Kraus.wordSpan (tensor D) 1 from by
          simpa using Kraus.pow_mem_wordSpan' (tensor D) 1 1)
      rw [jump_return hD] at hm
      have hlen : 1 + (n + 1) * (D - 1) = 1 + n * (D - 1) + (D - 2) + 1 := by
        rw [Nat.add_mul, one_mul]
        omega
      rw [← hlen] at hm
      exact hm

/-- The source's exact-length constraint suffices for membership of a
shifted jump. Source: arXiv:0909.5347, source lines 697–700. -/
theorem sandwich_mem_wordSpan (hD : 2 ≤ D) (k l n m : ℕ) :
    shift D ^ k * jump D * shift D ^ l ∈
      Kraus.wordSpan (tensor D) (1 + k + l + n * (D - 1) + m * D) := by
  have hm := mul_mem
    (mul_mem (mul_mem (shift_pow_mem k) (jump_mem_wordSpan hD n)) (shift_pow_mem l))
    (shift_pow_mem (m * D))
  rw [shift_pow_mul_dim, mul_one] at hm
  have hlen : k + (1 + n * (D - 1)) + l + m * D =
      1 + k + l + n * (D - 1) + m * D := by omega
  rwa [hlen] at hm

/-- All reduced pairs except the final pair have padding to `D(D-1)`.
Source: arXiv:0909.5347, source lines 697–700, with the missing diagonal
handled separately as documented in the module's local-fix note. -/
omit [NeZero D] in
theorem exists_full_length_padding (hD : 2 ≤ D) {k l : ℕ}
    (hk : k < D) (hl : l < D) (hexcept : ¬(k = D - 1 ∧ l = D - 1)) :
    ∃ n m : ℕ, D * (D - 1) = 1 + k + l + n * (D - 1) + m * D := by
  have hdim : D - 1 + 1 = D := by omega
  by_cases hs : k + l ≤ D - 2
  · refine ⟨k + l + 1, D - (k + l) - 2, ?_⟩
    have hm : D - (k + l) - 2 + k + l + 2 = D := by omega
    nlinarith
  · refine ⟨k + l + 1 - D, 2 * D - (k + l) - 3, ?_⟩
    have hn : k + l + 1 - D + D = k + l + 1 := by omega
    have hm : 2 * D - (k + l) - 3 + k + l + 3 = 2 * D := by omega
    nlinarith

private theorem single_mem_of_ne_zero_pair (hD : 2 ≤ D) (i j : Fin D)
    (hij : ¬(i = 0 ∧ j = 0)) :
    Matrix.single i j (1 : ℂ) ∈ Kraus.wordSpan (tensor D) (D * (D - 1)) := by
  let k := (i - 1).val
  let l := (((D - 1 : ℕ) : Fin D) - j).val
  have hk : k < D := (i - 1).isLt
  have hl : l < D := (((D - 1 : ℕ) : Fin D) - j).isLt
  have hexcept : ¬(k = D - 1 ∧ l = D - 1) := by
    rintro ⟨hk', hl'⟩
    apply hij
    have hkfin : i - 1 = ((D - 1 : ℕ) : Fin D) := by
      rw [← Fin.cast_val_eq_self (i - 1), show (i - 1).val = D - 1 from hk']
    have hlfin : ((D - 1 : ℕ) : Fin D) - j = ((D - 1 : ℕ) : Fin D) := by
      rw [← Fin.cast_val_eq_self (((D - 1 : ℕ) : Fin D) - j),
        show (((D - 1 : ℕ) : Fin D) - j).val = D - 1 from hl']
    constructor
    · calc
        i = 1 + (i - 1) := by abel
        _ = 1 + ((D - 1 : ℕ) : Fin D) := by rw [hkfin]
        _ = 0 := one_add_last hD
    · have heq := sub_add_cancel (((D - 1 : ℕ) : Fin D)) j
      rw [hlfin] at heq
      simpa only [add_eq_left] using heq
  obtain ⟨n, m, hlen⟩ := exists_full_length_padding hD hk hl hexcept
  have hm := sandwich_mem_wordSpan hD k l n m
  rw [← hlen, sandwich_eq_single] at hm
  have hrow : (1 : Fin D) + (k : Fin D) = i := by
    dsimp [k]
    rw [Fin.cast_val_eq_self]
    abel
  have hcol : ((D - 1 : ℕ) : Fin D) - (l : Fin D) = j := by
    dsimp [l]
    rw [Fin.cast_val_eq_self]
    abel
  rwa [hrow, hcol] at hm

/-- The cyclic example has full exact-word span at length `D(D-1)`.
Source: arXiv:0909.5347, source lines 691–700, including the local
missing-diagonal correction recorded in the module docstring. -/
theorem wordSpan_full_length (hD : 2 ≤ D) :
    Kraus.wordSpan (tensor D) (D * (D - 1)) = ⊤ := by
  let T := Kraus.wordSpan (tensor D) (D * (D - 1))
  have hI : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ T := by
    have hm := shift_pow_mem (D := D) (D * (D - 1))
    have hpow : shift D ^ (D * (D - 1)) = 1 := by
      rw [Nat.mul_comm D (D - 1), shift_pow_mul_dim]
    rw [hpow] at hm
    exact hm
  have hrest : (∑ i ∈ Finset.univ.erase (0 : Fin D), Matrix.single i i (1 : ℂ)) ∈ T := by
    apply T.sum_mem
    intro i hi
    exact single_mem_of_ne_zero_pair hD i i (by
      have hi0 := (Finset.mem_erase.mp hi).1
      tauto)
  have hzero : Matrix.single (0 : Fin D) 0 (1 : ℂ) ∈ T := by
    have hsplit := Finset.add_sum_erase Finset.univ
      (fun i : Fin D ↦ Matrix.single i i (1 : ℂ)) (Finset.mem_univ (0 : Fin D))
    rw [Matrix.sum_single_one] at hsplit
    have hunit : Matrix.single (0 : Fin D) 0 (1 : ℂ) =
        1 - ∑ i ∈ Finset.univ.erase (0 : Fin D), Matrix.single i i (1 : ℂ) :=
      eq_sub_iff_add_eq.mpr hsplit
    rw [hunit]
    exact T.sub_mem hI hrest
  apply T.eq_top_of_forall_single_mem
  intro i j
  by_cases hij : i = 0 ∧ j = 0
  · simpa [hij.1, hij.2] using hzero
  · exact single_mem_of_ne_zero_pair hD i j hij

end MPSTensor.CyclicWielandt

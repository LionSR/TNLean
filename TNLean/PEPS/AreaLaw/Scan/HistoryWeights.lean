/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Positivity

/-!
# Classical weights of actual scanner histories

The initial random choices are one uniform offset in `Fin m` for each band. Each
charge then makes an independent uniform choice in `Bool × Fin M` in every band.
The fixed padding length `M` makes the same finite choice space valid at every
history, including choices of blank slots. A fill is deterministic and adds no
random choice. Consequently `History K m M k` records exactly the random choices
after `k` completed fill/charge pairs.

These are classical path probabilities, before any replica state is transported.
No state-dependent measure or assumed sampling certificate enters the weights.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  `08-scanner.tex`, lines 83–154 (offsets, padded charge choices, and history weights).
-/

namespace TNLean.PEPS.AreaLaw.Scan

/-- The simultaneous side and padded-slot choices at one charge round.
`08-scanner.tex`, lines 122–135. -/
abbrev ChargeChoices (K M : ℕ) := Fin K → Bool × Fin M

/-- Initial offsets and all charge choices after `k` fill/charge pairs.
Fills add no random choices. `08-scanner.tex`, lines 83–154. -/
abbrev History (K m M k : ℕ) := (Fin K → Fin m) × (Fin k → ChargeChoices K M)

/-- Append one simultaneous charge choice, without changing initial offsets.
`08-scanner.tex`, lines 145–154. -/
def extendHistory {K m M k : ℕ} (h : History K m M k) (c : ChargeChoices K M) :
    History K m M (k + 1) :=
  (h.1, Fin.snoc h.2 c)

/-- Probability of the independent `K` side-and-slot choices at one charge.
`08-scanner.tex`, lines 122–135. -/
noncomputable def chargeWeight {K M : ℕ} (_c : ChargeChoices K M) : ℝ :=
  (1 / (2 * (M : ℝ))) ^ K

/-- Classical probability of a history: the product of its offset probabilities
and all its charge probabilities. `08-scanner.tex`, lines 83–154. -/
noncomputable def historyWeight {K m M k : ℕ} (_h : History K m M k) : ℝ :=
  (1 / (m : ℝ)) ^ K * ((1 / (2 * (M : ℝ))) ^ K) ^ k

/-- The finite number of histories, including blank choices.
`08-scanner.tex`, lines 83–154. -/
@[simp] theorem card_history (K m M k : ℕ) :
    Fintype.card (History K m M k) = m ^ K * ((2 * M) ^ K) ^ k := by
  simp [History, ChargeChoices]

/-- Every charge path weight is nonnegative. `08-scanner.tex`, lines 122–135. -/
theorem chargeWeight_nonneg {K M : ℕ} (c : ChargeChoices K M) : 0 ≤ chargeWeight c := by
  unfold chargeWeight
  positivity

/-- Every history path weight is nonnegative. `08-scanner.tex`, lines 145–154. -/
theorem historyWeight_nonneg {K m M k : ℕ} (h : History K m M k) :
    0 ≤ historyWeight h := by
  unfold historyWeight
  positivity

/-- The independent choices at one charge have total probability one.
`08-scanner.tex`, lines 122–135. -/
theorem sum_chargeWeight (K : ℕ) {M : ℕ} (hM : 0 < M) :
    ∑ c : ChargeChoices K M, chargeWeight c = 1 := by
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  simp [chargeWeight, ChargeChoices, Nat.cast_mul, Nat.cast_pow,
    ← mul_pow, mul_assoc, hM0]

/-- Classical path probabilities of all histories sum to one.
`08-scanner.tex`, lines 145–154. -/
theorem sum_historyWeight (K k : ℕ) {m M : ℕ} (hm : 0 < m) (hM : 0 < M) :
    ∑ h : History K m M k, historyWeight h = 1 := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  simp only [historyWeight, Finset.sum_const, Finset.card_univ, card_history,
    nsmul_eq_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [mul_mul_mul_comm]
  simp [← mul_pow, mul_assoc, hm0, hM0]

/-- Appending a charge multiplies the old probability by the same independent
charge probability at every old history. `08-scanner.tex`, lines 122–154. -/
theorem historyWeight_extendHistory {K m M k : ℕ} (h : History K m M k)
    (c : ChargeChoices K M) :
    historyWeight (extendHistory h c) = historyWeight h * chargeWeight c := by
  simp [historyWeight, chargeWeight, pow_succ, mul_assoc]

/-- All continuations of one history have the old history's total weight.
`08-scanner.tex`, lines 145–154. -/
theorem sum_historyWeight_extendHistory {K m M k : ℕ} (h : History K m M k)
    (hM : 0 < M) :
    ∑ c : ChargeChoices K M, historyWeight (extendHistory h c) = historyWeight h := by
  simp_rw [historyWeight_extendHistory]
  rw [← Finset.mul_sum, sum_chargeWeight K hM, mul_one]

/-- A designated band's side-and-slot pair has probability exactly `1 / (2M)`.
The other bands' choices are summed out. `08-scanner.tex`, lines 122–135. -/
theorem sum_chargeWeight_band {K M : ℕ} (hM : 0 < M) (g : Fin K)
    (a : Bool × Fin M) :
    ∑ c : ChargeChoices K M, (if c g = a then chargeWeight c else 0) =
      1 / (2 * (M : ℝ)) := by
  cases K with
  | zero => exact Fin.elim0 g
  | succ K =>
    have hcard : (Finset.univ.filter fun c : ChargeChoices (K + 1) M ↦ c g = a).card =
        (2 * M) ^ K := by
      simpa [ChargeChoices] using
        Fintype.card_filter_piFinset_const_eq_of_mem (Finset.univ : Finset (Bool × Fin M))
          g (Finset.mem_univ a)
    have hM0 : (M : ℝ) ≠ 0 := by positivity
    rw [← Finset.sum_filter]
    simp only [chargeWeight, Finset.sum_const, nsmul_eq_mul, hcard,
      Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
    rw [one_div, pow_succ, ← mul_assoc, ← mul_pow,
      mul_inv_cancel₀ (mul_ne_zero two_ne_zero hM0), one_pow, one_mul]

/-- Given any old history, a designated band's side-and-slot pair receives exactly
its uniform share of the old history's mass. `08-scanner.tex`, lines 122–154. -/
theorem sum_historyWeight_extendHistory_band {K m M k : ℕ} (h : History K m M k)
    (hM : 0 < M) (g : Fin K) (a : Bool × Fin M) :
    ∑ c : ChargeChoices K M, (if c g = a then historyWeight (extendHistory h c) else 0) =
      historyWeight h * (1 / (2 * (M : ℝ))) := by
  rw [← Finset.sum_filter]
  simp_rw [historyWeight_extendHistory]
  rw [← Finset.mul_sum, Finset.sum_filter, sum_chargeWeight_band hM g a]

/-- Each initial band's offset remains uniform after all completed charge rounds.
`08-scanner.tex`, lines 83–88 and 145–154. -/
theorem sum_historyWeight_offset {K m M k : ℕ} (hm : 0 < m) (hM : 0 < M)
    (g : Fin K) (a : Fin m) :
    ∑ h : History K m M k, (if h.1 g = a then historyWeight h else 0) = 1 / (m : ℝ) := by
  cases K with
  | zero => exact Fin.elim0 g
  | succ K =>
    have hoff : (∑ r : Fin (K + 1) → Fin m,
        if r g = a then (1 / (m : ℝ)) ^ (K + 1) else 0) = 1 / (m : ℝ) := by
      have hcard : (Finset.univ.filter fun r : Fin (K + 1) → Fin m ↦ r g = a).card =
          m ^ K := by
        simpa using Fintype.card_filter_piFinset_const_eq_of_mem
          (Finset.univ : Finset (Fin m)) g (Finset.mem_univ a)
      have hm0 : (m : ℝ) ≠ 0 := by positivity
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, hcard, Nat.cast_pow]
      rw [one_div, pow_succ, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hm0,
        one_pow, one_mul]
    have hc : (∑ c : Fin k → ChargeChoices (K + 1) M,
        ((1 / (2 * (M : ℝ))) ^ (K + 1)) ^ k) = 1 := by
      have h := congrArg (fun x : ℝ ↦ x ^ k) (sum_chargeWeight (K + 1) hM)
      rw [Fintype.sum_pow] at h
      simpa [chargeWeight] using h
    calc
      _ = (∑ r : Fin (K + 1) → Fin m,
          if r g = a then (1 / (m : ℝ)) ^ (K + 1) else 0) *
          (∑ c : Fin k → ChargeChoices (K + 1) M,
            ((1 / (2 * (M : ℝ))) ^ (K + 1)) ^ k) := by
        rw [Fintype.sum_prod_type, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c _
        by_cases hr : r g = a <;> simp [historyWeight, hr]
      _ = 1 / (m : ℝ) := by rw [hoff, hc, mul_one]

end TNLean.PEPS.AreaLaw.Scan

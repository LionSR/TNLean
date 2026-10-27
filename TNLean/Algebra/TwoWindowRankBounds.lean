/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Counting factors in a two-window expansion

For a polynomial degree bound `k`, a local dimension `d`, a window size `ℓ`
and a frequency bound `b`, the sum of the two-window counting factors is bounded
by a product of powers. When `k ≥ 1`, `d ≥ 2`, `ℓ ≥ 1` and `b ≤ k`, that product
is at most `(d * k) ^ (17 * (ℓ + b))`. Every degree from zero through `k` is retained.
Application to a Hamiltonian requires the separate operator expansion and comparisons
of ranks across cuts.

**Local fix (count):** The ordered-gap factors used in the sum estimate retain the
additional `+1` documented in the QICLean paper-gap note:
https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf.

## References

ALVV, arXiv:1602.08828v2, `eq:H-mid-cut`, lines 810–821, and
Proposition 5.7 (`prop:Cheby-AGSP-eff`), lines 1324–1332.
-/

open scoped BigOperators

/-- A scalar bound for the rank factors in the two-window expansion.
This is an arithmetic auxiliary for ALVV, arXiv:1602.08828v2,
`eq:H-mid-cut`, lines 810–821, and `prop:Cheby-AGSP-eff`,
lines 1324–1332. The parameter `b` is any upper bound for the two
selected frequencies with `b ≤ k`; its quotient formula is used only
when applying this estimate to the expansion. -/
theorem Nat.two_window_rank_factor_le_pow (k d ℓ b : ℕ)
    (hk : 1 ≤ k) (hd : 2 ≤ d) (hℓ : 1 ≤ ℓ) (hb : b ≤ k) :
    (2 * ℓ) ^ 2 * (b + 1) ^ 2 * (k + 1) ^ (4 * ℓ + 1) *
      (2 * (k + 1)) ^ (4 * b + 2) * d ^ (4 * b + 4 * ℓ) ≤
      (d * k) ^ (17 * (ℓ + b)) := by
  have hdk : 2 * k ≤ d * k := Nat.mul_le_mul_right k hd
  have hbase : 2 ≤ d * k ∧ k + 1 ≤ d * k ∧ b + 1 ≤ d * k := by omega
  have hdX : d ≤ d * k := Nat.le_mul_of_pos_right d (by omega)
  have hℓX : 2 * ℓ ≤ (d * k) ^ ℓ :=
    (Nat.mul_le_pow (by decide : 2 ≠ 1) ℓ).trans (Nat.pow_le_pow_left hbase.1 ℓ)
  have hgap : 2 * (k + 1) ≤ (d * k) ^ 2 :=
    (Nat.mul_le_mul hbase.1 hbase.2.1).trans_eq (pow_two _).symm
  refine (Nat.mul_le_mul
    (Nat.mul_le_mul
      (Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.pow_le_pow_left hℓX 2) (Nat.pow_le_pow_left hbase.2.2 2))
        (Nat.pow_le_pow_left hbase.2.1 _))
      (Nat.pow_le_pow_left hgap _))
    (Nat.pow_le_pow_left hdX _)).trans ?_
  simp only [← pow_mul, ← pow_add]
  exact Nat.pow_le_pow_right (by omega) (by omega)

/-- A uniform bound for the sum of the two-window rank factors.
This is an arithmetic auxiliary for ALVV, arXiv:1602.08828v2,
`eq:H-mid-cut`, lines 810–821, and `prop:Cheby-AGSP-eff`,
lines 1324–1332. Every degree from zero through `k` is retained;
the two ordered-gap binomial coefficients include their upper-argument
correction. -/
theorem Nat.two_window_rank_sum_le_factor (k d ℓ b : ℕ)
    (hd : 1 ≤ d) (hb : b ≤ k) :
    (2 * ℓ) ^ 2 *
      (∑ r ∈ Finset.range (k + 1),
        ∑ i ∈ Finset.range (b + 1),
          ∑ j ∈ Finset.range (b + 1),
            (r + 1) ^ (4 * ℓ) *
              ((r + i + 1).choose (2 * i + 1) *
                (r + j + 1).choose (2 * j + 1) *
                d ^ (2 * (i + j) + 4 * ℓ))) ≤
      (2 * ℓ) ^ 2 * (b + 1) ^ 2 * (k + 1) ^ (4 * ℓ + 1) *
        (2 * (k + 1)) ^ (4 * b + 2) * d ^ (4 * b + 4 * ℓ) := by
  have hchoose (r i : ℕ) (hr : r ≤ k) (hi : i ≤ b) :
      (r + i + 1).choose (2 * i + 1) ≤ (2 * (k + 1)) ^ (2 * b + 1) :=
    (Nat.choose_le_pow _ _).trans
      ((Nat.pow_le_pow_left (by omega : r + i + 1 ≤ 2 * (k + 1)) _).trans
        (Nat.pow_le_pow_right (by omega : 0 < 2 * (k + 1)) (by omega)))
  have hgap (r i j : ℕ) (hr : r ≤ k) (hi : i ≤ b) (hj : j ≤ b) :
      (r + i + 1).choose (2 * i + 1) * (r + j + 1).choose (2 * j + 1) ≤
        (2 * (k + 1)) ^ (4 * b + 2) := by
    simpa only [← pow_add, show 2 * b + 1 + (2 * b + 1) = 4 * b + 2 by omega] using
      Nat.mul_le_mul (hchoose r i hr hi) (hchoose r j hr hj)
  let H := (k + 1) ^ (4 * ℓ) *
    ((2 * (k + 1)) ^ (4 * b + 2) * d ^ (4 * b + 4 * ℓ))
  have hterm (r i j : ℕ) (hr : r ≤ k) (hi : i ≤ b) (hj : j ≤ b) :
      (r + 1) ^ (4 * ℓ) *
        ((r + i + 1).choose (2 * i + 1) * (r + j + 1).choose (2 * j + 1) *
          d ^ (2 * (i + j) + 4 * ℓ)) ≤ H :=
    Nat.mul_le_mul (Nat.pow_le_pow_left (by omega : r + 1 ≤ k + 1) _)
      (Nat.mul_le_mul (hgap r i j hr hi hj)
        (Nat.pow_le_pow_right (by omega : 0 < d) (by omega)))
  have hsum := Finset.sum_le_sum (s := Finset.range (k + 1)) fun r hr ↦
    Finset.sum_le_sum (s := Finset.range (b + 1)) fun i hi ↦
      Finset.sum_le_sum (s := Finset.range (b + 1)) fun j hj ↦
        hterm r i j (Nat.le_of_lt_succ (Finset.mem_range.mp hr))
          (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
          (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul] at hsum
  refine (Nat.mul_le_mul_left ((2 * ℓ) ^ 2) hsum).trans_eq ?_
  simp only [H, pow_succ (k + 1) (4 * ℓ), pow_two (b + 1)]
  ac_rfl

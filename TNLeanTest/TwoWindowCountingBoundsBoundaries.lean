/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FrequencyCounts
import TNLean.Algebra.TwoWindowRankBounds

/-! # Boundary applications of degree sums and two-window counting bounds -/

open scoped BigOperators

-- The constant degree is included.
example : (∑ r ∈ Finset.range 1,
    Nat.card {α : Fin 3 → ℕ // (∑ a, α a) = r ∧ α 0 = 0 ∧ α 1 = 0}) ≤ 1 := by
  simpa using Nat.sum_card_fun_sum_eq_and_two_eq_le (I := Fin 3) (s := 0)
    (by decide) (0 : Fin 3) 1 (by decide) 0 0 0

-- With one remaining coordinate, the degree aggregate is sharp for every k.
example (k : ℕ) : (∑ r ∈ Finset.range (k + 1),
    Nat.card {α : Fin 3 → ℕ // (∑ a, α a) = r ∧ α 0 = 0 ∧ α 1 = 0}) = k + 1 := by
  simp_rw [Nat.card_fun_sum_eq_and_two_eq_of_total (I := Fin 3) (s := 0)
    (by decide) (0 : Fin 3) 1 (by decide)]
  simp

-- Seven original labels give the two-window exponent s + 1 = 5.
example : (∑ r ∈ Finset.range 2,
    Nat.card {α : Fin 7 → ℕ // (∑ a, α a) = r ∧ α 0 = 0 ∧ α 1 = 0}) ≤ 32 := by
  simpa only [show ((1 + 1) : ℕ) ^ (4 + 1) = 32 from by decide] using
    Nat.sum_card_fun_sum_eq_and_two_eq_le (I := Fin 7) (s := 4)
      (by decide) (0 : Fin 7) 1 (by decide) 1 0 0

example : (32768 : ℕ) ≤ 131072 :=
  Nat.two_window_rank_factor_le_pow 1 2 1 0 (by decide) (by decide) (by decide) (by decide)

example : (536870912 : ℕ) ≤ 17179869184 :=
  Nat.two_window_rank_factor_le_pow 1 2 1 1 (by decide) (by decide) (by decide) (by decide)

example (k d ℓ : ℕ) (hk : 1 ≤ k) (hd : 2 ≤ d) (hℓ : 1 ≤ ℓ) :
    let b := k / (2 * ℓ)
    (2 * ℓ) ^ 2 * (b + 1) ^ 2 * (k + 1) ^ (4 * ℓ + 1) *
      (2 * (k + 1)) ^ (4 * b + 2) * d ^ (4 * b + 4 * ℓ) ≤
      (d * k) ^ (17 * (ℓ + b)) :=
  Nat.two_window_rank_factor_le_pow k d ℓ (k / (2 * ℓ)) hk hd hℓ (Nat.div_le_self _ _)

example : (4 : ℕ) ≤ 16 :=
  Nat.two_window_rank_sum_le_factor 0 1 1 0 (by decide) (by decide)

example : (260 : ℕ) ≤ 2048 :=
  Nat.two_window_rank_sum_le_factor 1 1 1 0 (by decide) (by decide)

example (k d b : ℕ) (hd : 1 ≤ d) (hb : b ≤ k) :
    let ℓ : ℕ := 0
    (2 * ℓ) ^ 2 *
      (∑ r ∈ Finset.range (k + 1),
        ∑ i ∈ Finset.range (b + 1),
          ∑ j ∈ Finset.range (b + 1),
            (r + 1) ^ (4 * ℓ) *
              ((r + i + 1).choose (2 * i + 1) *
                (r + j + 1).choose (2 * j + 1) *
                d ^ (2 * (i + j) + 4 * ℓ))) ≤
      (2 * ℓ) ^ 2 * (b + 1) ^ 2 * (k + 1) ^ (4 * ℓ + 1) *
        (2 * (k + 1)) ^ (4 * b + 2) * d ^ (4 * b + 4 * ℓ) :=
  Nat.two_window_rank_sum_le_factor k d 0 b hd hb

example (k d ℓ : ℕ) (hd : 1 ≤ d) :
    let b := k / (2 * ℓ)
    (2 * ℓ) ^ 2 *
      (∑ r ∈ Finset.range (k + 1),
        ∑ i ∈ Finset.range (b + 1),
          ∑ j ∈ Finset.range (b + 1),
            (r + 1) ^ (4 * ℓ) *
              ((r + i + 1).choose (2 * i + 1) *
                (r + j + 1).choose (2 * j + 1) *
                d ^ (2 * (i + j) + 4 * ℓ))) ≤
      (2 * ℓ) ^ 2 * (b + 1) ^ 2 * (k + 1) ^ (4 * ℓ + 1) *
        (2 * (k + 1)) ^ (4 * b + 2) * d ^ (4 * b + 4 * ℓ) :=
  Nat.two_window_rank_sum_le_factor k d ℓ (k / (2 * ℓ)) hd (Nat.div_le_self _ _)

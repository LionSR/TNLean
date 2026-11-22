/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Depth bounds with conditioning varying between tree levels

The merging estimate of Styliaris--Trivedi--Cirac gives a recurrence
`T (j + 1) ≤ q j * (2 * T j + C * 2 ^ (j + 1))`. Here `q j` bounds the
conditioning costs at level `j`, and `C` bounds the local overhead.
Keeping the product of the level costs gives
`T L ≤ 2 ^ L * (a + C * L) * ∏ j < L, q j` when `T 0 ≤ a` and `q j ≥ 1`.
In particular, a polynomial bound on this product is sufficient for a
polynomial depth bound, up to a logarithmic factor.

These are numerical consequences of an assumed recurrence. No MPU circuit
construction or bound on the conditioning of a tensor is asserted here.
The level costs need not be bounded independently of the chain length.

Source context: arXiv:2508.08160v2, `references/2508.08160/main.tex`,
Merging Lemma `lem:merging`, lines 2145--2156, and the depth recurrence
in the proof of Theorem `prop:app:main`, lines 2380--2422.
The bounds with varying conditioning are derived here.
-/

open scoped BigOperators

namespace MPUCircuit

/-- A merging recurrence is controlled by the product of its level costs.
For `N = 2 ^ L`, the remaining factor `L` is logarithmic in the chain length.

Source context: arXiv:2508.08160v2, `references/2508.08160/main.tex`,
Merging Lemma `lem:merging`, lines 2145--2156, and the depth recurrence
in the proof of Theorem `prop:app:main`, lines 2380--2422. -/
theorem depth_le_prod_conditioning (T q : ℕ → ℝ) (a C : ℝ)
    (hC : 0 ≤ C) (hq : ∀ j, 1 ≤ q j) (hbase : T 0 ≤ a)
    (hstep : ∀ j, T (j + 1) ≤ q j * (2 * T j + C * 2 ^ (j + 1))) (L : ℕ) :
    T L ≤ 2 ^ L * (a + C * L) * ∏ j ∈ Finset.range L, q j := by
  induction L with
  | zero => simpa using hbase
  | succ L ih =>
    have hprod : 1 ≤ ∏ j ∈ Finset.range L, q j :=
      Finset.one_le_prod₀ fun j _ => hq j
    have hq₀ : 0 ≤ q L := le_trans (by norm_num) (hq L)
    refine (hstep L).trans ?_
    calc
      _ ≤ q L * (2 * (2 ^ L * (a + C * L) * ∏ j ∈ Finset.range L, q j) +
          C * 2 ^ (L + 1)) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 2))
            le_rfl) hq₀
      _ ≤ q L * (2 * (2 ^ L * (a + C * L) * ∏ j ∈ Finset.range L, q j) +
          C * 2 ^ (L + 1) * ∏ j ∈ Finset.range L, q j) := by
        exact mul_le_mul_of_nonneg_left
          (add_le_add le_rfl
            (le_mul_of_one_le_right (by positivity : (0 : ℝ) ≤ C * 2 ^ (L + 1))
              hprod)) hq₀
      _ = _ := by
        rw [Finset.prod_range_succ, pow_succ, Nat.cast_add, Nat.cast_one]
        ring

/-- A polynomial bound on the product of level conditioning costs gives a
polynomial depth bound with a logarithmic prefactor. The number of sites is
`2 ^ L`; the exponent `c` and the constants `a,C` are supplied explicitly.

This is a consequence of the merging recurrence, rather than a claim that
every MPU satisfies the product bound. -/
theorem depth_le_polynomial_of_prod_conditioning (T q : ℕ → ℝ) (a C : ℝ)
    (ha : 0 ≤ a) (hC : 0 ≤ C) (hq : ∀ j, 1 ≤ q j) (hbase : T 0 ≤ a)
    (hstep : ∀ j, T (j + 1) ≤ q j * (2 * T j + C * 2 ^ (j + 1)))
    (L c : ℕ) (hprod : (∏ j ∈ Finset.range L, q j) ≤ ((2 : ℝ) ^ L) ^ c) :
    T L ≤ (a + C * L) * ((2 : ℝ) ^ L) ^ (c + 1) := by
  refine (depth_le_prod_conditioning T q a C hC hq hbase hstep L).trans ?_
  calc
    _ ≤ 2 ^ L * (a + C * L) * ((2 : ℝ) ^ L) ^ c :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = _ := by
      rw [pow_succ]
      ring

/-- With a single conditioning cost, the product bound becomes
`(a + C * L) * (2 * q) ^ L`. It remains valid at `q = 1`.

Source context: arXiv:2508.08160v2, `references/2508.08160/main.tex`,
the displayed depth recurrence at lines 2395--2422. -/
theorem depth_le_constant_conditioning (T : ℕ → ℝ) (a C q : ℝ)
    (hC : 0 ≤ C) (hq : 1 ≤ q) (hbase : T 0 ≤ a)
    (hstep : ∀ j, T (j + 1) ≤ q * (2 * T j + C * 2 ^ (j + 1))) (L : ℕ) :
    T L ≤ (a + C * L) * (2 * q) ^ L := by
  simpa [Finset.prod_const, mul_pow, mul_assoc, mul_comm, mul_left_comm] using
    depth_le_prod_conditioning T (fun _ => q) a C hC (fun _ => hq) hbase hstep L

/-- The sequence `C * L * 2 ^ L` satisfies the merging recurrence with
conditioning equal to one and initial depth zero. Thus that recurrence alone
does not remove the logarithmic factor at the endpoint.

This is a numerical example, not a lower bound for an MPU implementation. -/
theorem linear_overhead_recurrence (C : ℝ) (L : ℕ) :
    C * (L + 1 : ℕ) * (2 : ℝ) ^ (L + 1) =
      2 * (C * L * (2 : ℝ) ^ L) + C * (2 : ℝ) ^ (L + 1) := by
  rw [Nat.cast_add, Nat.cast_one, pow_succ]
  ring

end MPUCircuit

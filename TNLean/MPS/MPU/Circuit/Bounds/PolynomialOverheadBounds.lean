/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Balanced recursion with polynomial overhead

Reversible tests of initialized registers have polynomial cost in the
interval length. At level `j` of a balanced binary recursion, an overhead
of degree `b` is bounded by a constant times `(2^b)^j`. A fixed child-call
factor greater than this growth factor absorbs the overhead into its own
geometric bound. Taking a binary upper bound on that factor then gives a
polynomial in the interval length `2^L`.

These are numerical consequences of a recurrence; circuit existence is
a separate assertion. Source: the cost estimate in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

namespace MPUCircuit

/-- A geometric overhead is absorbed when the child-call factor exceeds its
growth factor by at least one. Source: the cost estimate in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cost_le_pow_of_geometric_overhead (T : ℕ → ℝ) (a C r q : ℝ)
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hr : q + 1 ≤ r) (hbase : T 0 ≤ a)
    (hstep : ∀ j, T (j + 1) ≤ r * T j + C * q ^ j) (L : ℕ) :
    T L ≤ (a + C) * r ^ L - C * q ^ L := by
  induction L with
  | zero => simpa using hbase
  | succ L ih =>
    have hr₀ : 0 ≤ r := by linarith
    refine (hstep L).trans ?_
    calc
      _ ≤ r * ((a + C) * r ^ L - C * q ^ L) + C * q ^ L :=
        add_le_add (mul_le_mul_of_nonneg_left ih hr₀) le_rfl
      _ ≤ (a + C) * r ^ (L + 1) - C * q ^ (L + 1) := by
        rw [pow_succ, pow_succ]
        nlinarith [mul_nonneg (sub_nonneg.mpr hr) (mul_nonneg hC (pow_nonneg hq L))]

/-- A fixed branching factor bounded by `2^k` gives a degree-`k` polynomial
bound in the interval length. The polynomial overhead is supplied through
its geometric growth factor. Source: the cost estimate in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cost_le_polynomial_of_geometric_overhead (T : ℕ → ℝ) (a C r q : ℝ)
    (ha : 0 ≤ a) (hC : 0 ≤ C) (hq : 0 ≤ q) (hr : q + 1 ≤ r)
    (hbase : T 0 ≤ a) (hstep : ∀ j, T (j + 1) ≤ r * T j + C * q ^ j)
    (k L : ℕ) (hrk : r ≤ (2 : ℝ) ^ k) :
    T L ≤ (a + C) * ((2 : ℝ) ^ L) ^ k := by
  refine (cost_le_pow_of_geometric_overhead T a C r q hC hq hr hbase hstep L).trans ?_
  calc
    _ ≤ (a + C) * r ^ L := sub_le_self _ (mul_nonneg hC (pow_nonneg hq L))
    _ ≤ (a + C) * ((2 : ℝ) ^ k) ^ L :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hrk L) (add_nonneg ha hC)
    _ = _ := by rw [← pow_mul, ← pow_mul, Nat.mul_comm k L]

/-- An integer child-call factor gives an explicit polynomial exponent,
its binary ceiling logarithm. Source: the cost estimate in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cost_le_polynomial_clog_of_geometric_overhead (T : ℕ → ℝ)
    (a C q : ℝ) (r : ℕ) (ha : 0 ≤ a) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hr : q + 1 ≤ (r : ℝ)) (hbase : T 0 ≤ a)
    (hstep : ∀ j, T (j + 1) ≤ (r : ℝ) * T j + C * q ^ j) (L : ℕ) :
    T L ≤ (a + C) * ((2 : ℝ) ^ L) ^ Nat.clog 2 r := by
  apply cost_le_polynomial_of_geometric_overhead T a C r q ha hC hq hr hbase hstep
  exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) r

end MPUCircuit

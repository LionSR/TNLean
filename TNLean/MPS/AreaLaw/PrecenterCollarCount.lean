/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Lean.Elab.Tactic.Omega

/-!
# Collar cardinality within the fixed soft-family budget

The polynomial family parameter already dominates the matrix-unit cost
of collars of at most four window widths. No filter degree or suppression
parameter is changed by this estimate. Supporting ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1332–1333, with the explicitly
chosen coarse family count rather than a printed sharp rate.
-/

namespace TNLean.MPS.AreaLaw

/-- The fixed pre-center family parameter dominates the full collar
matrix-unit factor for four window widths. Supporting ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1332–1333. -/
theorem precenter_count_ge_collar_factor (q m k ell : ℕ)
    (hq : 1 ≤ q) (hk : 1 ≤ k) :
    q ^ (8 * ell) ≤ (m * k + 1) * (q * k) ^ (36 * ell + 4 * (k / ell)) := by
  have hqk : q ≤ q * k := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left q hk
  have hbase : 1 ≤ q * k := hq.trans hqk
  have hexp : 8 * ell ≤ 36 * ell + 4 * (k / ell) := by omega
  calc
    q ^ (8 * ell) ≤ (q * k) ^ (8 * ell) := pow_le_pow_left₀ (Nat.zero_le q) hqk _
    _ ≤ (q * k) ^ (36 * ell + 4 * (k / ell)) := pow_le_pow_right₀ hbase hexp
    _ ≤ (m * k + 1) * (q * k) ^ (36 * ell + 4 * (k / ell)) :=
      le_mul_of_one_le_left (Nat.zero_le _) (Nat.succ_le_succ (Nat.zero_le _))

/-- Enlarging one common family by at most four window widths keeps its
cardinality within the square of the SAME pre-center family parameter.
Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1332–1333.
No larger filter or suppression budget is introduced. -/
theorem common_collar_count_le_precenter_square (q m k ell n c : ℕ)
    (hq : 1 ≤ q) (hk : 1 ≤ k) (hc : c ≤ 4 * ell) :
    let D := (m * k + 1) * (q * k) ^ (36 * ell + 4 * (k / ell))
    n ≤ D → n * q ^ (2 * c) ≤ D ^ 2 := by
  intro D hn
  have hfactor : q ^ (2 * c) ≤ D :=
    (pow_le_pow_right₀ hq (by omega : 2 * c ≤ 8 * ell)).trans
      (precenter_count_ge_collar_factor q m k ell hq hk)
  simpa only [pow_two] using Nat.mul_le_mul hn hfactor

end TNLean.MPS.AreaLaw

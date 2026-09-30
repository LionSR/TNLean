/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Character sums over binary configurations

The characters of the group of binary configurations `ι → Fin 2` are the sign
functions `a ↦ ∏ i, (-1) ^ (a i * c i)`. Summing such a character over all
configurations gives `2 ^ |ι|` for the trivial character `c = 0` and zero otherwise.
This orthogonality relation is the step that turns a contraction of two
Kramers–Wannier kernels into a delta constraint.

The file also records the elementary bit identities used alongside it: a sum of two bits
vanishes exactly when they agree, adding a fixed configuration is an involution, a sum of
two bits equals one exactly when they are complementary, and a sign `(-1) ^ n` squares
to one.
-/

/-- Two bits add to zero exactly when they agree. -/
theorem Fin.add_eq_zero_iff_eq (u v : Fin 2) : u + v = 0 ↔ u = v := by
  revert u v; decide

/-- Adding a fixed binary configuration moves across an equation of configurations,
`c = d + e ↔ d = c + e`. -/
theorem Fin.pi_eq_add_iff_eq_add {ι : Type*} (c d e : ι → Fin 2) :
    c = d + e ↔ d = c + e := by
  simp only [funext_iff, Pi.add_apply]
  refine forall_congr' fun i => ?_
  generalize c i = x, d i = y, e i = z
  revert x y z; decide

/-- Two bits add to one exactly when they are complementary. -/
theorem Fin.add_eq_one_iff_eq_rev (u v : Fin 2) : u + v = 1 ↔ u = v.rev := by
  revert u v; decide

/-- A sign `(-1) ^ n` squares to one. -/
theorem neg_one_pow_mul_neg_one_pow_self {R : Type*} [Monoid R] [HasDistribNeg R] (n : ℕ) :
    (-1 : R) ^ n * (-1 : R) ^ n = 1 := by
  rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

namespace Fintype

open scoped BigOperators

/-- Orthogonality of the characters of `ι → Fin 2`: the sum over all binary
configurations `a` of `∏ i, (-1) ^ (a i * c i)` equals `2 ^ |ι|` if `c = 0` and
vanishes otherwise. The exponent is computed in the natural numbers. -/
theorem sum_prod_neg_one_pow_val_mul {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (c : ι → Fin 2) :
    ∑ a : ι → Fin 2, ∏ i, (-1 : R) ^ ((a i).val * (c i).val) =
      if c = 0 then (2 : R) ^ Fintype.card ι else 0 := by
  rw [← Fintype.prod_sum (fun i (x : Fin 2) => (-1 : R) ^ (x.val * (c i).val))]
  have h (y : Fin 2) :
      ∑ x : Fin 2, (-1 : R) ^ (x.val * y.val) = if y = 0 then 2 else 0 := by
    fin_cases y <;> simp [Fin.sum_univ_two]
  simp_rw [h]
  split_ifs with hc
  · simp [hc, Finset.prod_const, Finset.card_univ]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hc
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [show c i ≠ 0 from hi])

end Fintype

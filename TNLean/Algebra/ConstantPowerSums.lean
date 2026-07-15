/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.Order
import Mathlib.Data.Complex.BigOperators

/-!
# Constant power sums

A finite family of nonnegative real numbers whose power sums
$\sum_k x_k^L$ take the same value at every positive exponent $L$ has all
entries equal to $0$ or $1$: an entry exceeding one would make the power sums
unbounded, and comparing the exponents one and two then forces
$\sum_k x_k(1 - x_k) = 0$ with nonnegative summands.  The file also provides
the corresponding statement for families of complex numbers that are
nonnegative in the complex order.

These are the scalar inputs for the discussion following Theorem IV.13 of
arXiv:1606.00608 (lines 995--1010): structure coefficients of the form
$\operatorname{tr}(\chi^L)$ with positive diagonal $\chi$ that do not depend
on $L$ are natural numbers.  The paper derives this from its power-sum
uniqueness lemma (lines 1155--1163); the elementary argument here suffices for
the constant-power-sum specialization.

The nonnegativity hypothesis cannot be dropped: the primitive cube roots of
unity have power sums invariant under doubling the exponent, yet do not lie in
$\{0, 1\}$.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Section 4.5, lines 995--1010
-/

open scoped BigOperators ComplexOrder

variable {ι : Type*} [Fintype ι]

/-- Entries of a nonnegative real family whose power sums do not depend on the
positive exponent are at most one: an entry exceeding one would make the power
sums unbounded.

Source: arXiv:1606.00608, line 1010 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem le_one_of_forall_sum_pow_eq {x : ι → ℝ} (hx : ∀ k, 0 ≤ x k)
    (hsum : ∀ L : ℕ, 0 < L → ∑ k, x k ^ L = ∑ k, x k) (j : ι) : x j ≤ 1 := by
  by_contra hgt
  rw [not_le] at hgt
  obtain ⟨L, hL⟩ := pow_unbounded_of_one_lt (∑ k, x k) hgt
  have hsingle : x j ^ (L + 1) ≤ ∑ k, x k ^ (L + 1) :=
    Finset.single_le_sum (fun k _ => pow_nonneg (hx k) _) (Finset.mem_univ j)
  have hmono : x j ^ L ≤ x j ^ (L + 1) := pow_le_pow_right₀ hgt.le (Nat.le_succ L)
  have heq := hsum (L + 1) (Nat.succ_pos L)
  linarith

/-- **Constant power sums have entries zero or one.** If the power sums
`∑ k, x k ^ L` of a nonnegative real family do not depend on the positive
exponent `L`, then every entry equals `0` or `1`.

Comparing the exponents one and two shows that `∑ k, x k * (1 - x k)`
vanishes, and every summand is nonnegative because no entry exceeds one.

Source: arXiv:1606.00608, line 1010 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem eq_zero_or_eq_one_of_forall_sum_pow_eq {x : ι → ℝ} (hx : ∀ k, 0 ≤ x k)
    (hsum : ∀ L : ℕ, 0 < L → ∑ k, x k ^ L = ∑ k, x k) (j : ι) :
    x j = 0 ∨ x j = 1 := by
  have hle : ∀ k, x k ≤ 1 := le_one_of_forall_sum_pow_eq hx hsum
  have hzero : ∑ k, (x k - x k ^ 2) = 0 := by
    rw [Finset.sum_sub_distrib, hsum 2 two_pos, sub_self]
  have hterm : ∀ k ∈ Finset.univ, (0 : ℝ) ≤ x k - x k ^ 2 := by
    intro k _
    have hsq : x k ^ 2 ≤ x k := by
      rw [sq]
      exact mul_le_of_le_one_left (hx k) (hle k)
    linarith
  have hj := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hzero j (Finset.mem_univ j)
  rcases mul_eq_zero.mp (show x j * (1 - x j) = 0 by nlinarith) with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

/-- Complex version of the constant-power-sum dichotomy, for families that are
nonnegative in the complex order (real entries with nonnegative real part).
Nonnegativity cannot be dropped: the primitive cube roots of unity have power
sums invariant under doubling the exponent without lying in `{0, 1}`.

Source: arXiv:1606.00608, line 1010 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem Complex.eq_zero_or_eq_one_of_forall_sum_pow_eq {z : ι → ℂ}
    (hz : ∀ k, 0 ≤ z k)
    (hsum : ∀ L : ℕ, 0 < L → ∑ k, z k ^ L = ∑ k, z k) (j : ι) :
    z j = 0 ∨ z j = 1 := by
  have hre : ∀ k, z k = ((z k).re : ℂ) := by
    intro k
    have him : (z k).im = 0 := by
      have := (Complex.le_def).mp (hz k)
      simpa using this.2.symm
    exact Complex.ext rfl (by simp [him])
  have hxnonneg : ∀ k, 0 ≤ (z k).re := by
    intro k
    have := (Complex.le_def).mp (hz k)
    simpa using this.1
  have hsumR : ∀ L : ℕ, 0 < L → ∑ k, (z k).re ^ L = ∑ k, (z k).re := by
    intro L hL
    have hcast : ((∑ k, (z k).re ^ L : ℝ) : ℂ) = ((∑ k, (z k).re : ℝ) : ℂ) := by
      push_cast
      calc (∑ k, ((z k).re : ℂ) ^ L)
          = ∑ k, z k ^ L := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [← hre k]
        _ = ∑ k, z k := hsum L hL
        _ = ∑ k, ((z k).re : ℂ) := Finset.sum_congr rfl fun k _ => hre k
    exact_mod_cast hcast
  rcases _root_.eq_zero_or_eq_one_of_forall_sum_pow_eq hxnonneg hsumR j with h | h
  · left
    rw [hre j, h, Complex.ofReal_zero]
  · right
    rw [hre j, h, Complex.ofReal_one]

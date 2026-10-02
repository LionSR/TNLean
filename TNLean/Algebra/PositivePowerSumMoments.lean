/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Complex.Order
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Complex.BigOperators

/-!
# Finite moment tests for positive fusion spectra

For positive eigenvalues of an MPDO fusion matrix, three consecutive power sums
detect length independence. The second difference is a sum of weighted squares.

Source: arXiv:1606.00608, the question following Theorem 4.14. The moment
identities are elementary and proved here directly: the second difference
`p (n + 2) - 2 p (n + 1) + p n` of the power sums `p n = ∑ i, x i ^ n` equals
`∑ i, x i ^ n * (x i - 1) ^ 2`.
-/

open scoped BigOperators

namespace Real

variable {ι : Type*} [Fintype ι]

/-- The second difference of power sums is a sum of weighted squares. -/
theorem sum_pow_secondDifference (x : ι → ℝ) (n : ℕ) :
    (∑ i, x i ^ (n + 2)) - 2 * (∑ i, x i ^ (n + 1)) + ∑ i, x i ^ n =
      ∑ i, x i ^ n * (x i - 1) ^ 2 := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

/-- A vanishing second difference of three consecutive positive power sums
forces every weight to equal one. No bound on the number of weights is needed. -/
theorem eq_one_of_sum_pow_secondDifference_eq_zero {x : ι → ℝ} (n : ℕ)
    (hx : ∀ i, 0 < x i)
    (h : (∑ i, x i ^ (n + 2)) - 2 * (∑ i, x i ^ (n + 1)) + ∑ i, x i ^ n = 0)
    (i : ι) : x i = 1 := by
  rw [sum_pow_secondDifference] at h
  have hterm : x i ^ n * (x i - 1) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ ↦ mul_nonneg (pow_nonneg (hx j).le n) (sq_nonneg (x j - 1)))).mp h
        i (Finset.mem_univ i)
  have hsq : (x i - 1) ^ 2 = 0 :=
    (mul_eq_zero.mp hterm).resolve_left (ne_of_gt (pow_pos (hx i) n))
  simpa only [sq_eq_zero_iff, sub_eq_zero] using hsq

end Real

namespace Complex

open scoped ComplexOrder

variable {ι : Type*} [Fintype ι]

/-- The finite second-difference test for complex weights that are positive real
numbers under `ComplexOrder`. -/
theorem eq_one_of_sum_pow_secondDifference_eq_zero {x : ι → ℂ} (n : ℕ)
    (hx : ∀ i, 0 < x i)
    (h : (∑ i, x i ^ (n + 2)) - 2 * (∑ i, x i ^ (n + 1)) + ∑ i, x i ^ n = 0)
    (i : ι) : x i = 1 := by
  have hreal : ∀ j, x j = ((x j).re : ℂ) :=
    fun j ↦ Complex.eq_re_of_ofReal_le (hx j).le
  have hpow : ∀ k : ℕ, (∑ j, x j ^ k) = ((∑ j, (x j).re ^ k : ℝ) : ℂ) :=
    fun k ↦ by
      rw [Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun j _ ↦
        (congrArg (fun z : ℂ ↦ z ^ k) (hreal j)).trans (Complex.ofReal_pow _ _).symm
  rw [hpow (n + 2), hpow (n + 1), hpow n] at h
  have hr : (∑ j, (x j).re ^ (n + 2)) - 2 * (∑ j, (x j).re ^ (n + 1)) +
      ∑ j, (x j).re ^ n = 0 := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
      Complex.ofReal_ofNat, Complex.ofReal_zero] using h
  rw [hreal i]
  simpa only [Complex.ofReal_one] using
    congrArg Complex.ofReal
      (Real.eq_one_of_sum_pow_secondDifference_eq_zero n
        (fun j ↦ (Complex.pos_iff.mp (hx j)).1) hr i)

end Complex

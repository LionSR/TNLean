/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Equality in the finite Cauchy--Schwarz inequality

For a finite family of real numbers, this file characterizes equality in
\[
  \left(\sum_{i\in S} f_i\right)^2
    \leq |S|\sum_{i\in S} f_i^2.
\]
The proof uses the sum of the squared pairwise differences. It applies without a
nonemptiness assumption, so the empty and singleton cases are included.

## Main results

* `Finset.sum_pairwise_sq_sub`: the pairwise-difference form of the variance identity.
* `Finset.sq_sum_eq_card_mul_sum_sq_iff`: equality holds exactly when the family is
  constant on the finite set.

## References

* Wolf, *Quantum Channels & Operations*, Chapter 2, Proposition "SIC POVMs",
  equations (2.31)--(2.32); `Notes/WolfNoteTexSource/ch02_representations.tex`,
  lines 802--815
-/

open scoped BigOperators

namespace Finset

variable {ι : Type*} (s : Finset ι) (f : ι → ℝ)

/-- The sum of the squared pairwise differences equals twice the unnormalized variance.

This identity is valid for every finite set, including the empty set.

Source: Wolf, *Quantum Channels & Operations*, Chapter 2, Proposition "SIC POVMs",
equations (2.31)--(2.32); `Notes/WolfNoteTexSource/ch02_representations.tex`,
lines 802--815. The identity records the equality case used there. -/
lemma sum_pairwise_sq_sub :
    (∑ i ∈ s, ∑ j ∈ s, (f i - f j) ^ 2) =
      2 * ((s.card : ℝ) * ∑ i ∈ s, (f i) ^ 2 - (∑ i ∈ s, f i) ^ 2) := by
  calc
    (∑ i ∈ s, ∑ j ∈ s, (f i - f j) ^ 2) =
        ∑ i ∈ s, ∑ j ∈ s, ((f i) ^ 2 + (f j) ^ 2 - 2 * f i * f j) := by
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      ring
    _ = 2 * ((s.card : ℝ) * ∑ i ∈ s, (f i) ^ 2 - (∑ i ∈ s, f i) ^ 2) := by
      simp_rw [sum_sub_distrib, sum_add_distrib]
      simp only [sum_const, nsmul_eq_mul]
      have hcross :
          (∑ i ∈ s, ∑ j ∈ s, 2 * f i * f j) =
            2 * (∑ i ∈ s, f i) * (∑ j ∈ s, f j) := by
        calc
          (∑ i ∈ s, ∑ j ∈ s, 2 * f i * f j) =
              2 * (∑ i ∈ s, ∑ j ∈ s, f i * f j) := by
            symm
            rw [mul_sum]
            apply sum_congr rfl
            intro i hi
            rw [mul_sum]
            apply sum_congr rfl
            intro j hj
            ring
          _ = 2 * (∑ i ∈ s, f i) * (∑ j ∈ s, f j) := by
            rw [← sum_mul_sum]
            ring
      rw [hcross]
      rw [← mul_sum]
      ring

/-- Equality in the finite Cauchy--Schwarz inequality holds exactly when the family is
constant on the finite set.

The pairwise formulation treats the empty and singleton cases without separate
hypotheses: in both cases the constancy condition and the equality are automatic.

Source: Wolf, *Quantum Channels & Operations*, Chapter 2, Proposition "SIC POVMs",
equations (2.31)--(2.32); `Notes/WolfNoteTexSource/ch02_representations.tex`,
lines 802--815. -/
theorem sq_sum_eq_card_mul_sum_sq_iff :
    (∑ i ∈ s, f i) ^ 2 = s.card * ∑ i ∈ s, (f i) ^ 2 ↔
      ∀ i ∈ s, ∀ j ∈ s, f i = f j := by
  constructor
  · intro h i hi j hj
    have hsum : (∑ i ∈ s, ∑ j ∈ s, (f i - f j) ^ 2) = 0 := by
      rw [sum_pairwise_sq_sub]
      nlinarith
    have houter : ∀ x ∈ s, 0 ≤ ∑ y ∈ s, (f x - f y) ^ 2 := by
      intro x hx
      exact sum_nonneg fun y hy ↦ sq_nonneg _
    have hinner := (sum_eq_zero_iff_of_nonneg houter).mp hsum i hi
    have hterm :=
      (sum_eq_zero_iff_of_nonneg (fun y hy ↦ sq_nonneg (f i - f y))).mp hinner j hj
    nlinarith
  · intro h
    by_cases hs : s.Nonempty
    · obtain ⟨i, hi⟩ := hs
      have hf : ∀ j ∈ s, f j = f i := fun j hj ↦ h j hj i hi
      calc
        (∑ j ∈ s, f j) ^ 2 = ((s.card : ℝ) * f i) ^ 2 := by
          rw [sum_eq_card_nsmul hf]
          simp
        _ = s.card * ∑ j ∈ s, (f j) ^ 2 := by
          rw [sum_eq_card_nsmul (fun j hj ↦ congrArg (· ^ 2) (hf j hj))]
          ring
    · simp at hs
      simp [hs]

end Finset

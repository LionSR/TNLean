/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# Termwise product bounds and Cauchy--Schwarz for finite sums

If each term of a finite sum satisfies \(\|z_i\|\le c\,a_ib_i\) with \(c\ge0\),
then the triangle inequality and Cauchy--Schwarz give
\(\|\sum_i z_i\|\le c\sqrt{\sum_i a_i^2}\sqrt{\sum_i b_i^2}\).
This is the step that carries an overlap bound through a finite orthogonal
decomposition over spectator configurations.
-/

open scoped BigOperators

namespace Finset

/-- If \(\|z_i\|\le c\,a_ib_i\) for every \(i\in s\) and \(c\ge0\), then
\(\|\sum_{i\in s}z_i\|\le c\sqrt{\sum_{i\in s}a_i^2}\sqrt{\sum_{i\in s}b_i^2}\). -/
theorem norm_sum_le_mul_sqrt_mul_sqrt {ι E : Type*} [SeminormedAddCommGroup E]
    (s : Finset ι) (z : ι → E) (a b : ι → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i ∈ s, ‖z i‖ ≤ c * a i * b i) :
    ‖∑ i ∈ s, z i‖ ≤
      c * (Real.sqrt (∑ i ∈ s, a i ^ 2) * Real.sqrt (∑ i ∈ s, b i ^ 2)) := by
  refine (norm_sum_le s z).trans ((Finset.sum_le_sum h).trans ?_)
  simpa only [mul_assoc, ← Finset.mul_sum] using
    mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt s a b) hc

end Finset

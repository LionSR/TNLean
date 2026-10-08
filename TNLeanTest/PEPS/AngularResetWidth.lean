/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.AngularResetWidth

/-!
# Consumers of the uniform reset-width estimate

These examples check nonintegral exponents, zero endpoints, the smallest
allowed scale, and a width supplied independently of the scalar bound.
-/

open TNLean.PEPS.Approximation

example : ∃ L₀ : ℝ, 2 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
    ∀ s : ℝ, 4 * Real.log L ≤ s → ∀ w : ℝ,
      w ≤ 2 * (1 + Real.log s) ^ (1 / 2 : ℝ) + Real.log L → w < s := by
  simpa using exists_angular_reset_width_lt_of_slope (1 / 2) 2 1 1 4
    (by norm_num) (by norm_num) (by norm_num)

example : ∃ L₀ : ℝ, 2 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
    ∀ s : ℝ, Real.log L ≤ s → (0 : ℝ) ≤ (3 / 4) * s ∧ (3 / 4) * s < s := by
  obtain ⟨L₀, hL₀, h⟩ := exists_angular_reset_width_bound_of_slope 0 0 0 1 1
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨L₀, hL₀, fun L hL s hs ↦ ?_⟩
  simpa using (h L hL).2 s (by simpa using hs)

example (K C₃ C₄ c D : ℝ) (hc : 0 < c) (hD : 0 < D)
    (hCD : 4 * C₄ / c ≤ D) :
    ∃ L₀ : ℝ, 2 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      C₃ * (1 + Real.log (D * Real.log L)) ^ K + C₄ * Real.log L <
        c * (D * Real.log L) := by
  obtain ⟨L₀, hL₀, h⟩ :=
    exists_angular_reset_width_bound_of_slope K C₃ C₄ c D hc hD hCD
  refine ⟨L₀, hL₀, fun L hL ↦ ?_⟩
  obtain ⟨hcost, hstrict⟩ := (h L hL).2 (D * Real.log L) le_rfl
  exact hcost.trans_lt hstrict

example (C₃ : ℝ) : ∃ L₀ : ℝ, 2 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
    ∀ s : ℝ, Real.log L ≤ s → ∀ w : ℝ, w ≤ C₃ → w < s := by
  simpa using exists_angular_reset_width_lt_of_slope 0 C₃ 0 1 1
    (by norm_num) (by norm_num) (by norm_num)

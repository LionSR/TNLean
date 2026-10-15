/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RegularizedPatchRadiusDerivative
import TNLean.PEPS.AreaLaw.RegularizedPatchLogMinimum
import QICLean.Analysis.MinimumEnvelope
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-!
# Regularity of the original logarithmic patch minimum

On a bounded nonnegative radius interval, all feasible logarithmic patch
objectives have a common Lipschitz constant. Their attained minimum has that
same constant and is therefore absolutely continuous. No nesting of the
regions or regularity of a choice of minimizers is required. Nonnegative
weights, including a zero total weight and the empty product, are retained.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, September 24, 2026, `03-patches.tex`, lines 425–451,
`eq:patch-uniform-local-lipschitz`; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Set
open scoped BigOperators NNReal

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Out : V → Type*} [∀ v, Fintype (Out v)]
variable {m : ℕ} (regions : Fin m → Finset V)

/-- The logarithm of the actual ordered patch minimum inherits the common
Lipschitz constant of its feasible objectives. No differentiable selection
of minimizing tuples is needed.
Source: polynomial-PEPS manuscript, `03-patches.tex`, lines 433–451. -/
theorem lipschitzOnWith_log_regularizedPatchMinimum_exp_neg
    (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1))
    (hΩ : ‖Ω‖ = 1) (T : ℝ) (hT : 0 ≤ T) :
    let κ : ℝ := ∑ j, a j
    let K : ℝ≥0 := ⟨κ / 2 * (2 : ℝ) ^ (κ / 2) * Real.exp (κ * T / 2), by
      have hκ : 0 ≤ κ := Finset.sum_nonneg (fun j _ ↦ ha j)
      positivity⟩
    LipschitzOnWith K
      (fun R : ℝ ↦ Real.log (regularizedPatchMinimum regions a (Real.exp (-R)) Ω))
      (Icc 0 T) := by
  intro κ K
  apply lipschitzOnWith_of_isLeast
    (f := fun R x ↦ Real.log
      (regularizedPatchObjective regions a (Real.exp (-R)) Ω x))
    (S := regularizedPatchDomain (Out := Out) regions)
  · intro R _hR
    exact isLeast_log_regularizedPatchObjective regions a ha (Real.exp_pos (-R)) Ω hΩ
  · intro x hx
    have hder := exists_hasDerivAt_log_regularizedPatchObjective_exp_neg_uniform
      regions a ha Ω hΩ T hT x hx
    refine (convex_Icc (0 : ℝ) T).lipschitzOnWith_of_nnnorm_deriv_le ?_ ?_
    · intro R hR
      obtain ⟨d, hd, _hbound⟩ := hder R hR
      exact hd.differentiableAt
    · intro R hR
      obtain ⟨d, hd, hbound⟩ := hder R hR
      apply NNReal.coe_le_coe.mp
      change ‖deriv (fun r : ℝ ↦ Real.log
        (regularizedPatchObjective regions a (Real.exp (-r)) Ω x)) R‖ ≤
          κ / 2 * (2 : ℝ) ^ (κ / 2) * Real.exp (κ * T / 2)
      rw [hd.deriv, Real.norm_eq_abs]
      exact hbound

/-- The logarithm of the original patch minimum is absolutely continuous on
every bounded nonnegative radius interval, including a singleton interval.
Source: polynomial-PEPS manuscript, `03-patches.tex`, lines 433–451. -/
theorem absolutelyContinuousOnInterval_log_regularizedPatchMinimum_exp_neg
    (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1))
    (hΩ : ‖Ω‖ = 1) (T : ℝ) (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval
      (fun R : ℝ ↦ Real.log (regularizedPatchMinimum regions a (Real.exp (-R)) Ω))
      0 T := by
  have h := lipschitzOnWith_log_regularizedPatchMinimum_exp_neg regions a ha Ω hΩ T hT
  rw [← uIcc_of_le hT] at h
  exact h.absolutelyContinuousOnInterval

end TNLean.PEPS

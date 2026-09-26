/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Exponential sums on windows of consecutive integers

A nonzero exponential sum `∑ⱼ aⱼ μⱼ^t` with distinct unimodular frequencies
cannot be small at `K` consecutive integers: the Vandermonde map is injective,
hence bounded below.

This estimate is used for the decaying-correlation bound of
arXiv:2307.01696, Supplemental Material, proof of Lemma 2, when the subleading
eigenvalues of the transfer map are complex (chapter entry
`lem:ldp_vandermonde_window`).
-/

open scoped BigOperators

namespace Complex

/-- A nonzero exponential sum `∑ⱼ aⱼ μⱼ^t` with distinct unimodular frequencies
is bounded below, uniformly in `t`, at one of any `K` consecutive integers.

This is the Vandermonde estimate that replaces, for complex subleading
eigenvalues, the final step "the second and third [conditions] ensure
(auxform2) for sufficiently large `N`" of arXiv:2307.01696, Supplemental
Material, proof of Lemma 2: the leading part of the correlator is a sum over
the eigenvalues of modulus `|λ₂|`, which can vanish at individual separations.
The constant `c₀` is not made explicit. -/
lemma exists_window_le_norm_sum_mul_pow {K : ℕ} {μ : Fin K → ℂ}
    (hμ : Function.Injective μ) (hnorm : ∀ j, ‖μ j‖ = 1)
    {a : Fin K → ℂ} (ha : a ≠ 0) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ t : ℕ, ∃ u : Fin K,
      c₀ ≤ ‖∑ j, a j * μ j ^ (t + (u : ℕ))‖ := by
  classical
  let W : (Fin K → ℂ) →ₗ[ℂ] (Fin K → ℂ) :=
    { toFun := fun v u ↦ ∑ j, v j * μ j ^ (u : ℕ)
      map_add' := fun v w ↦ by
        funext u
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c v ↦ by
        funext u
        simp [Finset.mul_sum, mul_assoc] }
  have hW : Function.Injective W := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hμ
      (fun i ↦ congrFun hv i)
  obtain ⟨C, hCpos, hC⟩ := W.injective_iff_antilipschitz.mp hW
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  refine ⟨‖a‖ / ((C : ℝ) + 1), div_pos hapos (by positivity), ?_⟩
  intro t
  let b : Fin K → ℂ := fun j ↦ a j * μ j ^ t
  have hb : ‖a‖ ≤ ‖b‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg b)).mpr fun j ↦ ?_
    have : ‖a j‖ = ‖b j‖ := by simp [b, norm_pow, hnorm]
    rw [this]
    exact norm_le_pi_norm b j
  have hWb : ‖b‖ ≤ C * ‖W b‖ := by
    have := hC.le_mul_dist b 0
    simpa [dist_eq_norm] using this
  have hWb' : ‖a‖ / ((C : ℝ) + 1) ≤ ‖W b‖ := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg (W b), NNReal.coe_nonneg C]
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  have hlt : ‖W b‖ < ‖a‖ / ((C : ℝ) + 1) := by
    refine (pi_norm_lt_iff (div_pos hapos (by positivity))).mpr fun u ↦ ?_
    have hu := hcon u
    have : W b u = ∑ j, a j * μ j ^ (t + (u : ℕ)) := by
      simp [W, b, pow_add, mul_assoc]
    rw [this]
    exact hu
  exact absurd hWb' (not_le.mpr hlt)

end Complex

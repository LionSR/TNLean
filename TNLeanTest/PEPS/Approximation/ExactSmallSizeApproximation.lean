/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ExactSmallSizeApproximation

/-!
# Consumers of the exact small-size approximation

These examples check the model's Euclidean coordinate identification, complex
normalization scalar, unit norm, zero normalized error, ground-state consumer,
and the one-site, one-dimensional, zero-exponent endpoint.
-/

namespace TNLean.PEPS.Approximation

example {q L : ℕ} (hq : 0 < q) (hL : 0 < L)
    (Ω : StateSpace L q) (hΩ : ‖Ω‖ = 1) :
    ∃ A : Tensor (squareLatticeGraph L L) q,
      pepsVector A = Ω ∧ ‖pepsVector A‖ = 1 ∧
      ‖((‖pepsVector A‖⁻¹ : ℝ) : ℂ) • pepsVector A - (1 : ℂ) • Ω‖ = 0 := by
  obtain ⟨A, _, _, hvector, _, _⟩ :=
    ExactTreeRepresentation.exists_exact_unit_square_tensor hq hL Ω hΩ
  have hv : pepsVector A = Ω := hvector
  refine ⟨A, hv, ?_, ?_⟩
  · simpa only [hv] using hΩ
  · simp [hv, hΩ]

example {q L L₀ : ℕ} (hq : 2 ≤ q) (hL : 2 ≤ L) (hsmall : L < L₀)
    (C c J Δ E₀ : ℝ) (hc : 0 ≤ c) (h : SquareHamiltonian L q J)
    (Ω : StateSpace L q) (hΩ : h.IsGappedGroundState E₀ Ω Δ) :
    HasPEPSApproximation (max C (q ^ (L₀ * L₀) : ℕ)) c L q Ω :=
  hasPEPSApproximation_of_small_size (by omega) (by omega) hsmall.le C c hc Ω hΩ.1

example (Ω : StateSpace 1 1) (hΩ : ‖Ω‖ = 1) :
    HasPEPSApproximation 1 0 1 1 Ω := by
  simpa using hasPEPSApproximation_of_small_size
    (q := 1) (L := 1) (L₀ := 1) (by decide) (by decide) (by decide)
    0 0 (by norm_num) Ω hΩ

example {q L₀ : ℕ} (hq : 2 ≤ q) (J Δ c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧
      ∀ L : ℕ, 2 ≤ L → L < L₀ → ∀ h : SquareHamiltonian L q J,
        ∀ E₀ : ℝ, ∀ Ω : StateSpace L q,
          h.IsGappedGroundState E₀ Ω Δ → HasPEPSApproximation C c L q Ω := by
  obtain ⟨C, hC, _, huniform⟩ :=
    exists_uniform_small_size_approximation (q := q) (L₀ := L₀) (by omega) 0 c hc.le
  refine ⟨C, hC, ?_⟩
  intro L hL hsmall h E₀ Ω hΩ
  exact huniform L hL hsmall Ω hΩ.1

set_option linter.hashCommand false

/-- info: 'TNLean.PEPS.Approximation.hasPEPSApproximation_of_small_size' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.Approximation.hasPEPSApproximation_of_small_size

/-- info: 'TNLean.PEPS.Approximation.exists_uniform_small_size_approximation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.Approximation.exists_uniform_small_size_approximation

end TNLean.PEPS.Approximation

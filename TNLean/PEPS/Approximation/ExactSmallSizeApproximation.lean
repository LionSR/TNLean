/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.Basic
import TNLean.PEPS.Approximation.ExactSquareRepresentation

/-!
# Exact PEPS approximation for small squares

The exact finite-size representation satisfies the native approximation
predicate for every unit vector. Its normalized error is zero, and one enlarged
prefactor covers all positive side lengths below a fixed threshold.

The approximation uses the native PEPS convention on the original square.
Only the finite range of side lengths is covered here.

Source: *Polynomial PEPS approximation of gapped square-grid ground states*,
September 24, 2026, `07-assembly.tex`, lines 203–214, and the target convention in
`00-introduction.tex`, Theorem 1.1, at immutable manuscript revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TNLean.PEPS.Approximation

/-- Every unit vector on a smaller positive square satisfies the PEPS
approximation predicate with one enlarged prefactor. The exact contraction has
zero normalized error and phase zero. Source: manuscript, assembly, lines
203–214; this is only the finite-size part of Theorem 1.1. -/
theorem hasPEPSApproximation_of_small_size {q L L₀ : ℕ}
    (hq : 0 < q) (hL : 0 < L) (hsmall : L ≤ L₀)
    (C c : ℝ) (hc : 0 ≤ c) (Ω : StateSpace L q) (hΩ : ‖Ω‖ = 1) :
    HasPEPSApproximation (max C (q ^ (L₀ * L₀) : ℕ)) c L q Ω := by
  obtain ⟨A, hpos, hbound, hstate⟩ :=
    ExactTreeRepresentation.exists_exact_square_tensor_polynomial
      hq hL hsmall C c hc (WithLp.ofLp Ω)
  have hv : pepsVector A = Ω := by
    change WithLp.toLp 2 (stateCoeff A) = Ω
    rw [hstate, WithLp.toLp_ofLp]
  refine ⟨A, hpos, hbound, ?_, 0, ?_⟩
  · intro hzero
    have hnorm : ‖pepsVector A‖ = 1 := by simpa only [hv] using hΩ
    simp only [hzero, norm_zero, zero_ne_one] at hnorm
  · simp [hv, hΩ]

/-- One positive enlarged prefactor works for every side length in a fixed
finite range and every unit vector, with the constant chosen before either.
Source: manuscript, assembly, lines 203–214. -/
theorem exists_uniform_small_size_approximation {q L₀ : ℕ}
    (hq : 0 < q) (C c : ℝ) (hc : 0 ≤ c) :
    ∃ C' : ℝ, 0 < C' ∧ C ≤ C' ∧
      ∀ L : ℕ, 2 ≤ L → L < L₀ → ∀ Ω : StateSpace L q,
        ‖Ω‖ = 1 → HasPEPSApproximation C' c L q Ω := by
  refine ⟨max C (q ^ (L₀ * L₀) : ℕ), ?_, le_max_left _ _, ?_⟩
  · have hfinite : (0 : ℝ) < (q ^ (L₀ * L₀) : ℕ) := by
      exact_mod_cast (pow_pos hq (L₀ * L₀))
    exact hfinite.trans_le (le_max_right _ _)
  · intro L hL hsmall Ω hΩ
    exact hasPEPSApproximation_of_small_size hq (by omega) hsmall.le C c hc Ω hΩ

end TNLean.PEPS.Approximation

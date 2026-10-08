/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ExactFiniteException

/-!
# Consumers of finite-exception removal

These examples retain the native approximation predicate and check prefactor
monotonicity without a positive-size or exponent assumption, preservation of a
fixed exponent, and the full uniform quantifier order in both directions.
-/

namespace TNLean.PEPS.Approximation

example {L q : ℕ} {C c : ℝ} {Ω : StateSpace L q}
    (h : HasPEPSApproximation C c L q Ω) :
    HasPEPSApproximation (max C 1) c L q Ω :=
  h.mono_prefactor (le_max_left _ _)

example {q L₀ : ℕ} {J Δ C c : ℝ} (hq : 2 ≤ q) (hc : 0 < c)
    (hlarge : ∀ L : ℕ, 2 ≤ L → L₀ ≤ L → ∀ h : SquareHamiltonian L q J,
      ∀ E₀ : ℝ, ∀ Ω : StateSpace L q,
        h.IsGappedGroundState E₀ Ω Δ → HasPEPSApproximation C c L q Ω) :
    ∃ C' : ℝ, 0 < C' ∧ C ≤ C' ∧
      ∀ L : ℕ, 2 ≤ L → ∀ h : SquareHamiltonian L q J,
        ∀ E₀ : ℝ, ∀ Ω : StateSpace L q,
          h.IsGappedGroundState E₀ Ω Δ → HasPEPSApproximation C' c L q Ω :=
  exists_uniform_approximation_of_sufficiently_large (by omega) hc.le hlarge

example
    (hlarge : ∀ q : ℕ, 2 ≤ q → ∀ J Δ : ℝ, 0 < J → 0 < Δ →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ L₀ : ℕ,
        ∀ L : ℕ, 2 ≤ L → L₀ ≤ L → ∀ h : SquareHamiltonian L q J,
          ∀ E₀ : ℝ, ∀ Ω : StateSpace L q,
            h.IsGappedGroundState E₀ Ω Δ → HasPEPSApproximation C c L q Ω) :
    PolynomialPEPSApproximation :=
  polynomialPEPSApproximation_iff_sufficiently_large.mpr hlarge

example (h : PolynomialPEPSApproximation) :
    ∀ q : ℕ, 2 ≤ q → ∀ J Δ : ℝ, 0 < J → 0 < Δ →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ L₀ : ℕ,
        ∀ L : ℕ, 2 ≤ L → L₀ ≤ L → ∀ h : SquareHamiltonian L q J,
          ∀ E₀ : ℝ, ∀ Ω : StateSpace L q,
            h.IsGappedGroundState E₀ Ω Δ → HasPEPSApproximation C c L q Ω :=
  polynomialPEPSApproximation_iff_sufficiently_large.mp h

set_option linter.hashCommand false

/-- info: 'TNLean.PEPS.Approximation.HasPEPSApproximation.mono_prefactor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.Approximation.HasPEPSApproximation.mono_prefactor

/-- info: 'TNLean.PEPS.Approximation.exists_uniform_approximation_of_sufficiently_large' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.Approximation.exists_uniform_approximation_of_sufficiently_large

/-- info: 'TNLean.PEPS.Approximation.polynomialPEPSApproximation_iff_sufficiently_large' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.Approximation.polynomialPEPSApproximation_iff_sufficiently_large

end TNLean.PEPS.Approximation

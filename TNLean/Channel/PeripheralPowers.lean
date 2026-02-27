/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.PeripheralSpectrum

/-!
# Peripheral powers

This file provides small bridging lemmas used in the “periodicity removal” step
in the canonical-form construction (cf. Wolf Thm 6.6 style arguments).

The core root-of-unity statement already lives in
`TNLean/Channel/PeripheralSpectrum.lean` as
`peripheral_isRootOfUnity_of_pow_eigenvalue`.

Here we package the common hypothesis “the peripheral eigenvalue set is closed
under powers” into a form that can be fed into that theorem.
-/

open scoped BigOperators

section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- If `μ` is a peripheral eigenvalue and peripheral eigenvalues are closed under powers,
then every `μ^n` is an eigenvalue of `E`.

This is the exact hypothesis needed for `peripheral_isRootOfUnity_of_pow_eigenvalue`. -/
theorem hasEigenvalue_pow_of_mem_peripheralEigenvalues
    (E : V →ₗ[ℂ] V) (μ : ℂ)
    (_hμ : μ ∈ peripheralEigenvalues E)
    (hpow : ∀ n : ℕ, μ ^ n ∈ peripheralEigenvalues E) :
    ∀ n : ℕ, Module.End.HasEigenvalue E (μ ^ n) := by
  intro n
  exact (hpow n).1

/-- **Finite + closed under powers ⇒ root of unity** (via
`peripheral_isRootOfUnity_of_pow_eigenvalue`).

This is a convenient wrapper: if one can show that peripheral eigenvalues are
closed under powers (typically using multiplicative-domain theory), then every
peripheral eigenvalue must be a root of unity. -/
theorem peripheral_isRootOfUnity_of_pow_mem_peripheralEigenvalues
    [FiniteDimensional ℂ V]
    (E : V →ₗ[ℂ] V) (μ : ℂ)
    (hμ : μ ∈ peripheralEigenvalues E)
    (hpow : ∀ n : ℕ, μ ^ n ∈ peripheralEigenvalues E) :
    ∃ p : ℕ, 0 < p ∧ μ ^ p = 1 := by
  have hμ_norm : ‖μ‖ = 1 := hμ.2
  have hpow' : ∀ n : ℕ, Module.End.HasEigenvalue E (μ ^ n) :=
    hasEigenvalue_pow_of_mem_peripheralEigenvalues E μ hμ hpow
  exact peripheral_isRootOfUnity_of_pow_eigenvalue E μ hμ_norm hpow'

/-- **Finite peripheral eigenvalue set + global closure under powers ⇒ root of unity**.

This is the “set-level” version: assuming
`∀ μ ∈ peripheralEigenvalues E, ∀ n, μ^n ∈ peripheralEigenvalues E`, any
`μ ∈ peripheralEigenvalues E` is a root of unity.

We keep the proof as a thin wrapper around
`peripheral_isRootOfUnity_of_pow_mem_peripheralEigenvalues`. -/
theorem peripheral_isRootOfUnity_of_closed_powers
    [FiniteDimensional ℂ V]
    (E : V →ₗ[ℂ] V)
    (hclosed : ∀ μ : ℂ, μ ∈ peripheralEigenvalues E → ∀ n : ℕ,
      μ ^ n ∈ peripheralEigenvalues E)
    (μ : ℂ) (hμ : μ ∈ peripheralEigenvalues E) :
    ∃ p : ℕ, 0 < p ∧ μ ^ p = 1 := by
  exact peripheral_isRootOfUnity_of_pow_mem_peripheralEigenvalues E μ hμ (hclosed μ hμ)

end

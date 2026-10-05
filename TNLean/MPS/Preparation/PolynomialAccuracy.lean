/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Order.Floor.Semiring
import TNLean.MPS.Preparation.ApproximationError

/-!
# Polynomial approximation accuracy under uniform blocking

For the normalized periodic state of a normal tensor, the choice
`q = ⌈2 ξ (1 + η) log N⌉` gives approximation error at most `C N^(-η)`.
The constant is independent of the exponent `η`, the block length, and the number of blocks.
The exact-coefficient theorem uses the established second-order estimate at `γ = 1/4`.
For any fixed `0 < γ < 2`, the block length `q = ⌈ξ (1 + η) log N / γ⌉` gives the
same polynomial accuracy, with a constant that may depend on `γ` but not on `η`, `q`, or `M`.
The source's coefficient `2 ξ` is the case `γ = 1/2`; every coefficient above `ξ / 2` is
admissible.

Source: arXiv:2307.01696, p. 4, paragraph following Lemma 1. The stronger second-order
estimate supplies the exact coefficient in the displayed block length; substitution into
the printed first-order estimate alone does not establish it.

**Scope restriction (positive correlation length):** These equal-block results assume
`ξ > 0`. The construction in `TNLean/MPS/Preparation/AllLengthPolynomialAccuracy.lean`
proves the exact-coefficient bound at every sufficiently large chain length, using unequal
blocks or exact preparation. Zero correlation length remains outside that construction;
see `docs/paper-gaps/mswc24_polynomial_accuracy_uniform_blocks.tex`.
-/

private theorem mul_exp_le_polynomial (a : ℝ) {ξ η : ℝ} (hξ : 0 < ξ) {q M : ℕ}
    (hN : 2 ≤ M * q)
    (hblock : ξ * (1 + η) * Real.log (M * q) ≤ a * q) :
    (M : ℝ) * Real.exp (-a * q / ξ) ≤
      ((M * q : ℕ) : ℝ) ^ (-η) := by
  have hqpos : 0 < q := by
    by_contra h
    have hq0 : q = 0 := by omega
    simp [hq0] at hN
  have hNpos : 0 < ((M * q : ℕ) : ℝ) := by exact_mod_cast (show 0 < M * q by omega)
  have hMq : (M : ℝ) ≤ ((M * q : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_mul_of_pos_right M hqpos
  have hexponent : -a * q / ξ ≤
      -(1 + η) * Real.log (M * q) := by
    apply (div_le_iff₀ hξ).mpr
    nlinarith [hblock]
  calc
    (M : ℝ) * Real.exp (-a * q / ξ)
        ≤ ((M * q : ℕ) : ℝ) * Real.exp (-a * q / ξ) :=
      mul_le_mul_of_nonneg_right hMq (Real.exp_pos _).le
    _ = Real.exp (Real.log ((M * q : ℕ) : ℝ) + -a * q / ξ) := by
      rw [Real.exp_add, Real.exp_log hNpos]
    _ ≤ Real.exp (Real.log ((M * q : ℕ) : ℝ) + -(1 + η) * Real.log (M * q)) :=
      Real.exp_le_exp.mpr (add_le_add (le_refl _) hexponent)
    _ = ((M * q : ℕ) : ℝ) ^ (-η) := by
      rw [Real.rpow_def_of_pos hNpos]
      congr 1
      push_cast
      ring

open scoped ComplexOrder InnerProductSpace

namespace MPSTensor

/-- With equal blocks of length `q = ⌈2 ξ (1 + η) log N⌉` and `N = M q ≥ 2`,
the actual approximation error is at most `C N^(-η)` for one constant independent
of `η`, `q`, and `M`. Source: arXiv:2307.01696, p. 4, paragraph following Lemma 1. -/
theorem exists_approximationError_le_polynomial_of_uniformBlocks {d D : ℕ}
    (A : MPSTensor d D) (hN : Kraus.IsNormal A) (hA : IsLeftCanonical A)
    {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef) (htr : σ.trace = 1)
    (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    (hξ : 0 < correlationLength lam₂) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → ∀ (q M : ℕ),
      2 ≤ M * q →
      q = ⌈2 * correlationLength lam₂ * (1 + η) * Real.log (M * q)⌉₊ →
      1 - ‖⟪approximatingMPVState A σ q M, normalizedMPVState A (M * q)⟫_ℂ‖ ≤
        C * ((M * q : ℕ) : ℝ) ^ (-η) := by
  obtain ⟨C, hC, h⟩ := exists_approximationError_le_mul A hN hA hσ htr hfix hlam
    (γ := 1 / 4) (by norm_num) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro η _ q M hlength hq
  have : NeZero M := ⟨by
    intro hM
    simp [hM] at hlength⟩
  have hceil : 2 * correlationLength lam₂ * (1 + η) * Real.log (M * q) ≤ (q : ℝ) := by
    simpa only [← hq] using
      (Nat.le_ceil (2 * correlationLength lam₂ * (1 + η) * Real.log (M * q) : ℝ))
  exact (h q M).trans (mul_le_mul_of_nonneg_left
    (mul_exp_le_polynomial (2 * (1 / 4)) hξ hlength (by nlinarith [hceil])) hC.le)

/-- Fix `0 < γ < 2`. Equal blocks of length `q = ⌈ξ (1 + η) log N / γ⌉`,
with `N = M q ≥ 2`, give approximation error at most `C N^(-η)` for one constant
independent of `η`, `q`, and `M`. This is the polynomial-accuracy corollary of
arXiv:2307.01696, Lemma 1, eq. (17), using the established second-order estimate
at rate `γ / 2`. -/
theorem exists_approximationError_le_polynomial_of_rate {d D : ℕ}
    (A : MPSTensor d D) (hN : Kraus.IsNormal A) (hA : IsLeftCanonical A)
    {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef) (htr : σ.trace = 1)
    (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    (hξ : 0 < correlationLength lam₂) {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → ∀ (q M : ℕ),
      2 ≤ M * q →
      q = ⌈correlationLength lam₂ * (1 + η) * Real.log (M * q) / γ⌉₊ →
      1 - ‖⟪approximatingMPVState A σ q M, normalizedMPVState A (M * q)⟫_ℂ‖ ≤
        C * ((M * q : ℕ) : ℝ) ^ (-η) := by
  obtain ⟨C, hC, h⟩ := exists_approximationError_le_mul A hN hA hσ htr hfix hlam
    (γ := γ / 2) (by positivity) (by linarith)
  refine ⟨C, hC, ?_⟩
  intro η _ q M hlength hq
  have : NeZero M := ⟨by
    intro hM
    simp [hM] at hlength⟩
  have hceil : correlationLength lam₂ * (1 + η) * Real.log (M * q) / γ ≤ (q : ℝ) := by
    simpa only [← hq] using
      (Nat.le_ceil (correlationLength lam₂ * (1 + η) * Real.log (M * q) / γ : ℝ))
  have hblock : correlationLength lam₂ * (1 + η) * Real.log (M * q) ≤ γ * q := by
    have := (div_le_iff₀ hγ0).mp hceil
    nlinarith
  have herror := h q M
  rw [show 2 * (γ / 2) = γ by ring] at herror
  exact herror.trans (mul_le_mul_of_nonneg_left
    (mul_exp_le_polynomial γ hξ hlength hblock) hC.le)

end MPSTensor

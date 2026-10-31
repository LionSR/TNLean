/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# Incompatible overlapping one-dimensional local spaces

If a vector has a prescribed one-dimensional left window and a prescribed
one-dimensional right window, a nonzero two-by-two coefficient minor of
the left window forces the vector to vanish. This is the coefficient
form of the obstruction to two overlapping pure entangled windows.

This elementary tensor-product fact is used in investigating the actual
short-volume ground-state condition in SPWC10, arXiv:0909.5347,
Theorem 5, lines 850--880. It is not itself a counterexample to that theorem
or a claim about an assembled all-volume parent Hamiltonian.
-/

namespace MPSPreparation

/-- Two overlapping one-dimensional coefficient sections are incompatible
when the left window has a nonzero two-by-two minor. No global state,
rank equality or purity conclusion is supplied.
This is elementary finite tensor-product algebra underlying the
short-volume investigation of SPWC10, Theorem 5, lines 850--880. -/
theorem eq_zero_of_overlapping_one_dimensional_sections
    {α β γ : Type*} (W : α → β → ℂ) (V : β → γ → ℂ)
    (a₀ a₁ : α) (b₀ b₁ : β)
    (hminor : W a₀ b₀ * W a₁ b₁ - W a₀ b₁ * W a₁ b₀ ≠ 0)
    (ψ : α → β → γ → ℂ)
    (hleft : ∀ c, ∃ f : ℂ, ∀ a b, ψ a b c = f * W a b)
    (hright : ∀ a, ∃ g : ℂ, ∀ b c, ψ a b c = g * V b c) :
    ∀ a b c, ψ a b c = 0 := by
  classical
  let f : γ → ℂ := fun c ↦ Classical.choose (hleft c)
  let g : α → ℂ := fun a ↦ Classical.choose (hright a)
  have hL (a b c) : ψ a b c = f c * W a b := Classical.choose_spec (hleft c) a b
  have hR (a b c) : ψ a b c = g a * V b c := Classical.choose_spec (hright a) b c
  have hmatch (a b c) : f c * W a b = g a * V b c := (hL a b c).symm.trans (hR a b c)
  have hf (c : γ) : f c = 0 := by
    have hprod : (W a₀ b₀ * W a₁ b₁ - W a₀ b₁ * W a₁ b₀) * (f c) ^ 2 = 0 := by
      calc
        _ = (f c * W a₀ b₀) * (f c * W a₁ b₁) -
            (f c * W a₀ b₁) * (f c * W a₁ b₀) := by ring
        _ = (g a₀ * V b₀ c) * (g a₁ * V b₁ c) -
            (g a₀ * V b₁ c) * (g a₁ * V b₀ c) := by rw [hmatch, hmatch, hmatch, hmatch]
        _ = 0 := by ring
    have hpow := (mul_eq_zero.mp hprod).resolve_left hminor
    rw [pow_two] at hpow
    exact (mul_eq_zero.mp hpow).elim id id
  intro a b c
  rw [hL, hf, zero_mul]

end MPSPreparation

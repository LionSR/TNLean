/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.PositivePowerSumMoments
import TNLean.MPS.MPDO.LengthIndependentCoefficients

/-!
# A finite test for length-independent structure coefficients

For positive fusion weights, agreement of the structure coefficients at lengths
one, two, and three already implies agreement at every positive length.
This is a finite criterion for the special case discussed after Theorem 4.14
of arXiv:1606.00608; it does not assert that an arbitrary RFP has this property.
The proof uses the second-difference identity for positive power sums.
-/

open scoped BigOperators ComplexOrder

namespace MPOTensor

namespace DiagonalChiFamily

variable {I : Type*} {χ : DiagonalChiFamily I}

/-- Three equal consecutive trace powers force every positive fusion weight
to equal one. This finite criterion strengthens the all-length hypothesis in
the discussion after arXiv:1606.00608, Theorem 4.14. -/
theorem entry_eq_one_of_tracePowerCoeff_eq_at_three_lengths
    (hχ : χ.PosEntries) (α β γ : I) (n : ℕ)
    (h₁ : χ.tracePowerCoeff α β γ (n + 1) = χ.tracePowerCoeff α β γ n)
    (h₂ : χ.tracePowerCoeff α β γ (n + 2) = χ.tracePowerCoeff α β γ n)
    (k : Fin (χ.dim α β γ)) : χ.entry α β γ k = 1 := by
  apply Complex.eq_one_of_sum_pow_secondDifference_eq_zero n (hχ α β γ)
  change χ.tracePowerCoeff α β γ (n + 2) -
    2 * χ.tracePowerCoeff α β γ (n + 1) + χ.tracePowerCoeff α β γ n = 0
  rw [h₁, h₂]
  ring

end DiagonalChiFamily

namespace BNTLabelCoefficientFamily

variable {Λ : Type*} {c : BNTLabelCoefficientFamily Λ}

/-- For a positive trace-power presentation, agreement at lengths one, two,
and three is equivalent to length independence. This is a finite criterion
for the special case discussed after arXiv:1606.00608, Theorem 4.14. -/
theorem HasPositiveLengthChiTracePowerForm.lengthIndependent_iff_coeff_two_three
    {χ : DiagonalChiFamily Λ}
    (h : c.HasPositiveLengthChiTracePowerForm χ) (hχ : χ.PosEntries) :
    c.LengthIndependent ↔
      (∀ α β γ, c.coeff 2 α β γ = c.coeff 1 α β γ) ∧
      (∀ α β γ, c.coeff 3 α β γ = c.coeff 1 α β γ) := by
  constructor
  · intro hLI
    exact ⟨hLI 2 (by decide), hLI 3 (by decide)⟩
  · rintro ⟨h₂, h₃⟩
    apply h.lengthIndependent_of_forall_entry_eq_one
    intro α β γ k
    apply DiagonalChiFamily.entry_eq_one_of_tracePowerCoeff_eq_at_three_lengths
      hχ α β γ 1
    · rw [← h 2 (by decide), ← h 1 one_pos]
      exact h₂ α β γ
    · rw [← h 3 (by decide), ← h 1 one_pos]
      exact h₃ α β γ

end BNTLabelCoefficientFamily

end MPOTensor

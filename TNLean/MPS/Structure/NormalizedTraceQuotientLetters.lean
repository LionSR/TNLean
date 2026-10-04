/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Structure.TraceQuotientLetterCoordinates

/-!
# Normalized trace-quotient letters

An injective minimal tensor and a normalized coefficient identification imply that the
corresponding physical trace section is injective. Its Gram coordinates recover the physical
letters with the same normalization. This is an algebraic auxiliary step towards the
reconstruction discussed in arXiv:1010.3732, Section II.F.2, lines 953–993 of the local source.
The coefficient identification is used pointwise and is not assumed continuous; no
physical-gap implication is asserted.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix

namespace Matrix

/-- A normalized minimal coefficient identification derives section injectivity and
reconstructs the normalized physical letters in that section. -/
theorem traceQuotientLetters_of_normalized_linearEquiv {d r D : ℕ}
    (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (E : (Fin r → ℂ) ≃ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (G : Matrix (Fin d) (Fin d) ℂ) (F : Matrix (Fin d) (Fin r) ℂ) (α₂ κ : ℂ)
    (hα₂ : α₂ ≠ 0) (hκ : κ ≠ 0)
    (hG : ∀ j i, G j i = α₂ * Matrix.trace (A i * A j))
    (hE : ∀ x, E x = κ • Fintype.linearCombination ℂ A (F *ᵥ x)) :
    Function.Injective (G * F).mulVec ∧
      ∀ i, E (traceQuotientLetterCoordinates G F *ᵥ Pi.single i 1) = κ • A i := by
  have hPair := traceQuotientSection_pair A G F α₂ hG
  have hTrace : Function.Injective (MPSTensor.traceMulRightPi A) :=
    LinearMap.ker_eq_bot.mp (MPSTensor.traceMulRightPi_ker_eq_bot hA)
  have hInj : Function.Injective (G * F).mulVec := by
    intro x y hxy
    apply E.injective
    rw [hE, hE]
    apply congrArg (κ • ·)
    apply hTrace
    exact smul_right_injective _ hα₂ ((hPair x).symm.trans (hxy.trans (hPair y)))
  let Q := E.trans (LinearEquiv.smulOfNeZero ℂ
    (Matrix (Fin D) (Fin D) ℂ) κ⁻¹ (inv_ne_zero hκ))
  have hQ : ∀ x, Q x = Fintype.linearCombination ℂ A (F *ᵥ x) := by
    intro x
    change κ⁻¹ • E x = _
    rw [hE, smul_smul, inv_mul_cancel₀ hκ, one_smul]
  have hRecover := traceQuotientLetterCoordinates_recover A Q G F α₂ hG hInj
    (fun x => by rw [hQ]; exact hPair x)
  refine ⟨hInj, fun i => ?_⟩
  rw [hE]
  exact congrArg (κ • ·) ((hQ _).symm.trans (hRecover i))

end Matrix

/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.PiAlgebra.FundamentalTheoremComplete
import TNLean.MPS.Chain.SameStateBridge
import TNLean.MPS.Chain.TranslationInvariance

/-!
# TI Reduction Corollary (Section 5, arXiv:1804.04964)

For constant (translation-invariant) chains `(A, …, A)` and `(B, …, B)` with
`A` injective, `SameMPV` on the combined tensors gives
`B^i = X · A^i · X⁻¹` for a single `X ∈ GL(D, ℂ)`, so `B` is injective.

## Main results

* `ti_reduction_corollary` — from `SameMPV` on combined tensors
* `ti_reduction_of_sameState` — from `SameState` via the blocking bridge hypothesis

## References

* [arXiv:1804.04964](https://arxiv.org/abs/1804.04964), Section 5
-/

open scoped Matrix

namespace MPSChainTensor

variable {d D n : ℕ}

/-- **TI Reduction Corollary**.

If `A` is injective and the constant chains `(A, …, A)` and `(B, …, B)` satisfy
`SameMPV` on their combined tensors, then `B` is gauge equivalent to `A` and
`B` is injective. -/
theorem ti_reduction_corollary
    (A B : MPSTensor d D)
    (hn : 0 < n)
    (hA : MPSTensor.IsInjective A)
    (hMPV : MPSTensor.SameMPV
      (MPSTensor.chainCombinedTensor (fun _ : Fin n => A))
      (MPSTensor.chainCombinedTensor (fun _ : Fin n => B))) :
    (∃ X : GL (Fin D) ℂ, ∀ i : Fin d,
      B i = (X : Matrix _ _ ℂ) * A i * ((X⁻¹ : GL _ ℂ) : Matrix _ _ ℂ)) ∧
    MPSTensor.IsInjective B := by
  obtain ⟨X, hGauge⟩ := ti_tensors_single_gauge A B hn hA hMPV
  constructor
  · exact ⟨X, hGauge⟩
  · exact MPSTensor.isInjective_of_gaugeEquiv hA ⟨X, hGauge⟩

/-- **TI Reduction from SameState**.

Same conclusion as `ti_reduction_corollary`, from fixed-length `SameState`
at chain length `n ≥ 3` using the blocking bridge hypothesis. -/
theorem ti_reduction_of_sameState
    (hBridge : SameStateBridgeHyp d D)
    (A B : MPSTensor d D)
    (hn : 3 ≤ n)
    (hA : MPSTensor.IsInjective A)
    (hState : SameState (fun _ : Fin n => A) (fun _ : Fin n => B)) :
    (∃ X : GL (Fin D) ℂ, ∀ i : Fin d,
      B i = (X : Matrix _ _ ℂ) * A i * ((X⁻¹ : GL _ ℂ) : Matrix _ _ ℂ)) ∧
    MPSTensor.IsInjective B := by
  have hInj : IsInjective (fun _ : Fin n => A) := fun _ => hA
  have hMPV := sameMPV_chainCombined_of_sameState hBridge
    (fun _ : Fin n => A) (fun _ : Fin n => B) hInj hn hState
  exact ti_reduction_corollary A B (Nat.lt_of_lt_of_le (by omega) hn) hA hMPV

end MPSChainTensor

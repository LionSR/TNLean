/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.PiAlgebra.FundamentalTheoremComplete
import TNLean.MPS.Chain.SameStateBridge
import TNLean.MPS.Chain.TranslationInvariance

/-!
# TI Reduction Corollary (Section 5, arXiv:1804.04964)

Given two constant (TI) chains with the same combined tensor span, the
Fundamental Theorem forces them to be gauge equivalent via a single matrix.

More precisely: given a constant (TI) chain `fun _ => A` with `A` injective, and
another constant chain `fun _ => B` whose combined tensor generates the same MPV
family, the Fundamental Theorem gives a single gauge `X ∈ GL(D,ℂ)` such that
`B i = X * A i * X⁻¹` for all `i`. In particular, `B` is also injective (gauge
equivalent to an injective tensor), so within this constant-chain setting one
can pass to a TI injective description.

## Main results

* `ti_reduction_corollary` — from `SameMPV` on combined tensors: TI gauge
  equivalence plus injectivity of `B`.
* `ti_reduction_of_sameState` — from `SameState` (via the blocking bridge
  hypothesis): same conclusion.

## References

* [arXiv:1804.04964](https://arxiv.org/abs/1804.04964), Section 5
-/

open scoped Matrix

namespace MPSChainTensor

variable {d D n : ℕ}

/-- **TI Reduction Corollary** (Section 5, arXiv:1804.04964).

For constant (TI) chains `fun _ => A` and `fun _ => B` with `A` injective, if
their combined tensors generate the same MPV family, then `B` is gauge
equivalent to `A` via a single invertible matrix, and `B` is also injective.

This shows that translation invariance of the state forces translation
invariance of the tensor description (up to gauge). -/
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

/-- **TI Reduction from SameState** (via blocking bridge hypothesis).

The same conclusion as `ti_reduction_corollary`, but starting from fixed-length
`SameState` (trace agreement at chain length `n`) and the blocking bridge
hypothesis that upgrades this to `SameMPV` on combined tensors. -/
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

/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PiAlgebra.FundamentalTheoremComplete
import TNLean.MPS.Chain.TranslationInvariance

/-!
# TI Reduction Corollary (Section 5, arXiv:1804.04964)

For constant (translation-invariant) chains `(A, …, A)` and `(B, …, B)` with
`A` injective, `SameMPV` on the combined tensors gives
$B^i = X A^i X^{-1}$ for a single `X ∈ GL(D, ℂ)`, so `B` is injective.

## Main results

* `ti_reduction_corollary` — from `SameMPV` on combined tensors

## References

* [MGSPSC18] Molnar, Garre-Rubio, Pérez-García, Schuch, Cirac,
  *Normal projected entangled pair states generating the same state*,
  arXiv:1804.04964, Section 5 (Applications — translation invariance reduction).
  Source: `Papers/1804.04964/`
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
  exact ⟨⟨X, hGauge⟩, MPSTensor.isInjective_of_gaugeEquiv hA ⟨X, hGauge⟩⟩

end MPSChainTensor

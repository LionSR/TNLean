/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.PiAlgebra.FundamentalTheoremComplete
import TNLean.MPS.Chain.TranslationInvariance
import TNLean.MPS.Chain.SameStateBridge

/-!
# TI Reduction Corollary (Section 5, arXiv:1804.04964)

If an injective non-TI MPS chain produces a translation-invariant state, then a
TI injective MPS description with the same bond dimension exists.

More precisely: given a constant (TI) chain `fun _ => A` with `A` injective, and
another constant chain `fun _ => B` whose combined tensor generates the same MPV
family, the Fundamental Theorem gives a single gauge `X ∈ GL(D,ℂ)` such that
`B i = X * A i * X⁻¹` for all `i`. In particular, `B` is also injective (gauge
equivalent to an injective tensor), so one can always pass to a TI injective
description.

## Main results

* `ti_reduction_corollary` — from `SameMPV` on combined tensors: TI gauge
  equivalence plus injectivity of `B`.
* `ti_reduction_of_sameState` — from `SameState` (via the blocking bridge
  hypothesis): same conclusion.
* `ti_gaugeEquiv_isInjective` — gauge equivalent of an injective tensor is
  injective.

## References

* [arXiv:1804.04964](https://arxiv.org/abs/1804.04964), Section 5
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- Gauge equivalent of an injective tensor is injective. -/
theorem isInjective_of_gaugeEquiv {A B : MPSTensor d D}
    (hA : IsInjective A) (hGauge : GaugeEquiv A B) :
    IsInjective B := by
  obtain ⟨X, hX⟩ := hGauge
  rw [IsInjective, eq_top_iff]
  intro M _
  -- We need to show M ∈ span(range B).
  -- Since A is injective, X⁻¹ * M * X ∈ span(range A).
  -- Each A i maps to B i = X * A i * X⁻¹ ∈ span(range B).
  -- So M = X * (X⁻¹ * M * X) * X⁻¹ ∈ span(range B).
  have hM' : ((X⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) * M * (X : Matrix _ _ ℂ) ∈
      Submodule.span ℂ (Set.range A) := hA ▸ Submodule.mem_top
  have hConj : ∀ N ∈ Submodule.span ℂ (Set.range A),
      (X : Matrix _ _ ℂ) * N * ((X⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) ∈
        Submodule.span ℂ (Set.range B) := by
    intro N hN
    induction hN using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [← hX i]
      exact Submodule.subset_span (Set.mem_range.mpr ⟨i, rfl⟩)
    | zero => simp [Submodule.zero_mem]
    | add x y _ _ hx hy =>
      simp only [Matrix.mul_add, Matrix.add_mul]
      exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      have : (X : Matrix _ _ ℂ) * (c • x) * ((X⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) =
          c • ((X : Matrix _ _ ℂ) * x * ((X⁻¹ : GL _ ℂ) : Matrix _ _ ℂ)) := by
        simp [mul_comm c, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
      rw [this]
      exact Submodule.smul_mem _ c hx
  have key := hConj _ hM'
  have : (X : Matrix _ _ ℂ) *
      (((X⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) * M * (X : Matrix _ _ ℂ)) *
      ((X⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) = M := by
    simp [Matrix.mul_assoc]
  rwa [this] at key

end MPSTensor

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
  have hCombinedInj :
      MPSTensor.IsInjective (MPSTensor.chainCombinedTensor (fun _ : Fin n => A)) :=
    MPSTensor.chainCombinedTensor_isInjective _ ⟨0, hn⟩ hA
  obtain ⟨X, hX⟩ := MPSTensor.fundamentalTheorem_singleBlock hCombinedInj hMPV
  constructor
  · refine ⟨X, fun i => ?_⟩
    have := hX (finProdFinEquiv (⟨0, hn⟩, i))
    simpa [MPSTensor.chainCombinedTensor_apply] using this
  · exact MPSTensor.isInjective_of_gaugeEquiv hA ⟨X, fun i => by
      have := hX (finProdFinEquiv (⟨0, hn⟩, i))
      simpa [MPSTensor.chainCombinedTensor_apply] using this⟩

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

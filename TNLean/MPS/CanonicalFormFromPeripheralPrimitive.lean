/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalFormFromPrimitive
import TNLean.MPS.PeripheralToSpectralGap

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false

open scoped Matrix BigOperators
open Filter

namespace MPSTensor

/-- Builder lemma: derive `IsCanonicalForm` from *peripheral-spectrum* primitivity of each block.

This is a lightweight wrapper: we first turn peripheral primitivity of `transferMap` into the
existing `MPSTensor.IsPrimitive` predicate, then reuse
`MPSTensor.isCanonicalForm_of_primitive`. -/
theorem isCanonicalForm_of_peripheralPrimitive
    {d : ℕ} {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    {μ : Fin r → ℂ} {A : (k : Fin r) → MPSTensor d (dim k)}
    (hInj : ∀ k, IsInjective (A k))
    (hDS : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1)
    (hμanti : StrictAnti (fun k : Fin r => ‖μ k‖))
    (hμne : ∀ k, μ k ≠ 0)
    (hPrimPer :
      ∀ k, PeripheralSpectrum.IsPrimitive (transferMap (d := d) (D := dim k) (A k))) :
    MPSTensor.IsCanonicalForm (d := d) (μ := μ) A := by
  let hInjData : MPSTensor.HasInjectiveBlocks (d := d) A :=
    { block_injective := hInj }
  let hLeftData : MPSTensor.IsLeftCanonicalBlockFamily (d := d) A :=
    { leftCanonical := hDS }
  let hμData : MPSTensor.HasStrictOrderedNonzeroWeights μ :=
    { mu_strict_anti := hμanti, mu_ne_zero := hμne }
  let hOverlapData : MPSTensor.HasNormalizedSelfOverlap (d := d) A := by
    refine { overlap_tendsto_one := ?_ }
    intro k
    simpa using
      (MPSTensor.overlap_tendsto_one_of_peripheralPrimitive (A := A k) (hInj k) (hDS k)
        (hPrimPer k))
  exact MPSTensor.IsCanonicalForm.ofSeparatedData hInjData hLeftData hμData hOverlapData

end MPSTensor

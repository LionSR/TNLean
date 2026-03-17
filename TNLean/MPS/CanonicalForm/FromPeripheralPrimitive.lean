/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.FromPrimitive
import TNLean.MPS.Overlap.PeripheralToSpectralGap

/-!
# Canonical form from peripheral primitive blocks

This file is a downstream compatibility layer: it converts peripheral-spectrum primitivity of the
transfer maps into the existing spectral-gap notion `MPSTensor.HasPrimitiveFixedPoint`, and then
reuses `MPSTensor.isCanonicalForm_of_primitive`.
It does not produce canonical-form data from arbitrary input tensors.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- Build `IsCanonicalForm` from peripheral-spectrum primitivity of each block transfer map.

This is a compatibility wrapper: the actual work is delegated first to
`hasPrimitiveFixedPoint_of_peripheralPrimitive`, and then to
`isCanonicalForm_of_primitive`. As in the primitive-builder file, all blockwise injectivity /
normalization / ordering data are assumed as inputs. -/
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
  refine isCanonicalForm_of_primitive hInj hDS hμanti hμne ?_
  intro k
  exact hasPrimitiveFixedPoint_of_peripheralPrimitive
    (A := A k) (hInj k) (hDS k) (hPrimPer k)

end MPSTensor

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.FromPrimitive
import TNLean.MPS.Overlap.PeripheralToSpectralGap

/-!
# Canonical form from peripheral primitive blocks

This file converts peripheral-spectrum primitivity of the transfer maps into the existing
spectral-gap notion `MPSTensor.HasPrimitiveFixedPoint`, and then applies
`MPSTensor.isCanonicalForm_of_primitive`.
It does not produce canonical-form data from arbitrary input tensors.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- Build `IsCanonicalForm` from peripheral-spectrum primitivity of each block transfer map.

The proof first applies `hasPrimitiveFixedPoint_of_peripheralPrimitive`, and then
`isCanonicalForm_of_primitive`. As in the primitive fixed-point theorem, the blockwise
injectivity, normalization, weight ordering, and nonzero-weight hypotheses are assumed.

Source context: Perez-Garcia--Verstraete--Wolf--Cirac 2007,
Theorem Th:TIcanonical, lines 742--763, starts from an arbitrary
translation-invariant MPS representation.

**Scope restriction (peripheral-primitive block hypotheses):** this theorem assumes
injectivity, strict ordering of the weight moduli, nonzero weights, and peripheral-spectrum
primitivity for every block. Those hypotheses are not assumptions of PGVWC07
Theorem Th:TIcanonical. See
`docs/paper-gaps/pgvwc07_ti_canonical_form_scope.tex`. -/
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

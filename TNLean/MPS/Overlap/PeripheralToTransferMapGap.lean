/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Structure.PrimitivityBridge
import TNLean.Spectral.PeripheralToTransferMapGap

/-!
# Peripheral primitivity → matrix-product-vector overlap convergence

This file draws the state-level consequence of the channel-level connection built in
`TNLean.Spectral.PeripheralToTransferMapGap`: peripheral primitivity of the transfer map of
an injective (or irreducible) normalized tensor `A` implies that the self-overlap
`mpvOverlap A A N` converges to `1` as `N → ∞`.

## Main results

* `overlap_tendsto_one_of_peripheralPrimitive` — injective case.
* `overlap_tendsto_one_of_peripheralPrimitive_of_irreducible` — irreducible case.

Both are immediate corollaries of `MPSTensor.HasPrimitiveFixedPoint.overlap_tendsto_one`
(`TNLean.MPS.Structure.PrimitivityBridge`) applied to the complementary transfer-map gap
established in `TNLean.Spectral.PeripheralToTransferMapGap`.
-/

open scoped Matrix BigOperators
open Filter

namespace MPSTensor

/-- Peripheral primitivity implies the self-overlap converges to 1. -/
theorem overlap_tendsto_one_of_peripheralPrimitive
    {d D : ℕ} [NeZero D]
    (A : MPSTensor d D)
    (hInj : Kraus.IsInjective A)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : _root_.IsPrimitive (Kraus.transferMap (d := d) (D := D) A)) :
    Tendsto (fun N ↦ mpvOverlap (d := d) A A N) atTop (nhds (1 : ℂ)) := by
  classical
  have hP : MPSTensor.HasPrimitiveFixedPoint A :=
    hasPrimitiveFixedPoint_of_peripheralPrimitive (A := A) hInj hNorm hPrim
  simpa only using (MPSTensor.HasPrimitiveFixedPoint.overlap_tendsto_one (A := A) hP)

/-- As a corollary, peripheral primitivity plus irreducibility implies
self-overlap convergence to `1`. -/
theorem overlap_tendsto_one_of_peripheralPrimitive_of_irreducible
    {d D : ℕ} [NeZero D]
    (A : MPSTensor d D)
    (hIrr : Kraus.IsIrreducibleFamily A)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : _root_.IsPrimitive (Kraus.transferMap (d := d) (D := D) A)) :
    Tendsto (fun N ↦ mpvOverlap (d := d) A A N) atTop (nhds (1 : ℂ)) := by
  classical
  have hP : MPSTensor.HasPrimitiveFixedPoint A :=
    hasPrimitiveFixedPoint_of_peripheralPrimitive_of_irreducible (A := A) hIrr hNorm hPrim
  simpa only using (MPSTensor.HasPrimitiveFixedPoint.overlap_tendsto_one (A := A) hP)

end MPSTensor

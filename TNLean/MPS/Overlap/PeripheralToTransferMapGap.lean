/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Structure.PrimitiveFixedPoint
import TNLean.Spectral.PrimitiveOverlap
import QICLean.Kraus.PrimitiveFixedPoint.FromPeripheral

/-!
# Peripheral primitivity → matrix-product-vector overlap convergence

This file draws the state-level consequence of the channel-level connection built in
`QICLean.Kraus.PrimitiveFixedPoint.FromPeripheral`: peripheral primitivity of the
finite Kraus map of an irreducible normalized tensor `A` implies that the
self-overlap `mpvOverlap A A N` converges to `1` as `N → ∞`.

## Main results

* `IsPrimitiveMPS.overlap_tendsto_one`: a primitive MPS tensor has self-overlap
  converging to `1`, by `mpvOverlap_tendsto_one_of_transfer_spectralRadius_compl_lt_one`
  applied to the hypotheses recorded in the `IsPrimitiveMPS` structure.
* `overlap_tendsto_one_of_peripheralPrimitive_of_irreducible` — irreducible case,
  the corollary obtained from the complementary transfer-map gap established in
  `QICLean.Kraus.PrimitiveFixedPoint.FromPeripheral`.
-/

open scoped Matrix BigOperators Kraus
open Filter

namespace MPSTensor

/-- A primitive MPS tensor has self-overlap converging to 1.

This is a direct application of `mpvOverlap_tendsto_one_of_transfer_spectralRadius_compl_lt_one`
from `PrimitiveOverlap.lean`, using the hypotheses recorded in the `IsPrimitiveMPS`
structure. -/
theorem IsPrimitiveMPS.overlap_tendsto_one {d D : ℕ} [NeZero D]
    {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ} (hP : IsPrimitiveMPS A ρ) :
    Tendsto (fun N ↦ mpvOverlap (d := d) A A N) atTop (nhds (1 : ℂ)) :=
  mpvOverlap_tendsto_one_of_transfer_spectralRadius_compl_lt_one A
    hP.norm ρ hP.fixedPoint_is_fixed hP.fixedPoint_ne_zero hP.fixedPoint_psd
    hP.complementary_transfer_map_gap

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
  obtain ⟨_, hP⟩ : MPSTensor.HasPrimitiveFixedPoint A :=
    Kraus.hasPrimitiveFixedPoint_of_peripheralPrimitive_of_irreducible A hIrr hNorm hPrim
  simpa only using MPSTensor.IsPrimitiveMPS.overlap_tendsto_one hP

end MPSTensor

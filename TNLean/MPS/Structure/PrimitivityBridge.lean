/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Structure.PrimitiveFixedPoint
import TNLean.Spectral.PrimitiveOverlap

/-!
# MPV overlap convergence from complementary transfer-map gap primitivity

## Main results

* `IsPrimitiveMPS.overlap_tendsto_one`: a primitive MPS tensor has self-overlap converging
  to 1.
* `HasPrimitiveFixedPoint.overlap_tendsto_one`: existential formulation for the same
  conclusion.
-/

open Matrix Filter

open scoped Kraus

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

/-- Existential version: if `A` has a primitive fixed point, its self-overlap converges to 1. -/
theorem HasPrimitiveFixedPoint.overlap_tendsto_one {d D : ℕ} [NeZero D]
    {A : MPSTensor d D} (hP : HasPrimitiveFixedPoint A) :
    Tendsto (fun N ↦ mpvOverlap (d := d) A A N) atTop (nhds (1 : ℂ)) :=
  let ⟨_, h⟩ := hP
  MPSTensor.IsPrimitiveMPS.overlap_tendsto_one h

end MPSTensor

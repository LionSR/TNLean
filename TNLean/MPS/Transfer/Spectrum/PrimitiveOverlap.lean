/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.FixedPoint.MeanErgodic.FixedPointProjection
import QICLean.Channel.KrausMap.KrausMap
import QICLean.Kraus.Transfer
import TNLean.MPS.Transfer.Spectrum.TransferOperatorGapInjective
import TNLean.MPS.Transfer.Spectrum.MPVOverlapTrace
import Mathlib.Analysis.Matrix.PosDef
import QICLean.Kraus.PrimitiveFixedPoint
import TNLean.MPS.Tensor
import QICLean.Kraus.PrimitiveFixedPoint.Basic
import QICLean.Kraus.PrimitiveFixedPoint.FromPeripheral

/-!
# Primitive overlap limit (complementary transfer-map gap formulation)

This module derives the **primitive/aperiodic overlap normalization**

`mpvOverlap A A N → 1`

from a complementary transfer-map gap hypothesis
(cf. Wolf Theorem 6.7: a primitive TP map has trivial peripheral spectrum,
so its powers converge to the rank-one projection onto the stationary state).

More precisely, if a trace-preserving map `E` has a (nonzero) fixed point `ρ`, and the
spectral radius of the complementary map `N := E - fixedPointProj ρ` is strictly
less than `1`, then `LinearMap.trace (E^n) → 1`.

For MPS tensors, the identity

`LinearMap.trace ((Kraus.transferMap A)^N) = mpvOverlap A A N`

then yields `mpvOverlap A A N → 1`.

This matches the **primitive branch** of the Fundamental Theorem proofs
(Cirac--Pérez-García--Schuch--Verstraete, Rev. Mod. Phys. 93 (2021)).

We intentionally phrase primitivity as a **complementary transfer-map gap**
hypothesis. Connecting this to Wolf's characterizations (irreducible +
aperiodic, peripheral spectrum roots of unity, etc.) is a separate module.

## Peripheral primitivity → matrix-product-vector overlap convergence

This file draws the state-level consequence of the channel-level connection built in
`QICLean.Kraus.PrimitiveFixedPoint.FromPeripheral`: peripheral primitivity of the
finite Kraus map of an irreducible normalized tensor `A` implies that the
self-overlap `mpvOverlap A A N` converges to `1` as `N → ∞`.

### Main results

* `Kraus.HasComplementaryFixedPointGap.overlap_tendsto_one`: a primitive MPS tensor has self-overlap
  converging to `1`, by `mpvOverlap_tendsto_one_of_transfer_spectralRadius_compl_lt_one`
  applied to the hypotheses recorded in the `Kraus.HasComplementaryFixedPointGap` structure.
* `overlap_tendsto_one_of_peripheralPrimitive_of_irreducible` — irreducible case,
  the corollary obtained from the complementary transfer-map gap established in
  `QICLean.Kraus.PrimitiveFixedPoint.FromPeripheral`.
-/

open MPTensor

section

open scoped Matrix ComplexOrder BigOperators NNReal ENNReal Kraus
open Matrix Filter

namespace MPSTensor

section MPV

variable {d D : ℕ} [NeZero D]

/-- **Primitive overlap limit** (complementary transfer-map gap formulation).

If the transfer map of a normalized tensor `A` has a fixed point `ρ` and the
complement of the fixed-point projection has spectral radius less than `1`,
then the MPV self-overlap converges to `1`.
-/
theorem mpvOverlap_tendsto_one_of_transfer_spectralRadius_compl_lt_one
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : Kraus.transferMap (ι := Fin d) (n := Fin D) A ρ = ρ)
    (hρ_ne : ρ ≠ 0) (hρ_psd : ρ.PosSemidef)
    (hSpect :
      spectralRadius ℂ
          ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
            ((Kraus.transferMap (ι := Fin d) (n := Fin D) A) - fixedPointProj (D := D) ρ
              (by
                -- `trace ρ ≠ 0` for PSD nonzero `ρ`.
                intro htr0
                have : ρ = 0 := (Matrix.PosSemidef.trace_eq_zero_iff hρ_psd).1 htr0
                exact hρ_ne this))) < 1) :
    Filter.Tendsto (fun N => mpvOverlap (α := Fin d) A A N) Filter.atTop (nhds (1 : ℂ)) := by
  -- First derive `trace((Kraus.transferMap A)^N) → 1`.
  have hTP : IsTracePreservingMap (Kraus.transferMap (ι := Fin d) (n := Fin D) A) := by
    intro X
    exact Kraus.isTracePreservingMap_mapLM_of_isTP A hNorm X
  have htrρ : Matrix.trace ρ ≠ 0 := by
    intro htr0
    exact hρ_ne ((Matrix.PosSemidef.trace_eq_zero_iff hρ_psd).1 htr0)
  have hTrace :
      Filter.Tendsto
        (fun N => (LinearMap.trace ℂ (Matrix (Fin D) (Fin D) ℂ))
          ((Kraus.transferMap (ι := Fin d) (n := Fin D) A) ^ N))
        Filter.atTop (nhds (1 : ℂ)) :=
    LinearMap.trace_pow_tendsto_one_of_spectralRadius_compl_lt_one (D := D)
      (E := Kraus.transferMap (ι := Fin d) (n := Fin D) A) (ρ := ρ) (htr := htrρ) hTP hρ hSpect
  -- Rewrite the transfer-map trace as a mixed-transfer trace (self-case).
  have hTrace' :
      Filter.Tendsto
        (fun N => (LinearMap.trace ℂ (Matrix (Fin D) (Fin D) ℂ))
          ((Kraus.mixedMapLM (D₁ := D) (D₂ := D) A A) ^ N))
        Filter.atTop (nhds (1 : ℂ)) := by
    simpa [Kraus.mixedMapLM_self] using hTrace
  -- Now convert the trace identity to the MPV-overlap identity.
  simpa using
    (Filter.Tendsto.congr
      (fun N => (trace_mixedMapLM_pow_eq_mpvOverlap (A := A) (B := A) N))
      hTrace')

end MPV

end MPSTensor

end

section

open scoped Matrix BigOperators Kraus
open Filter

namespace MPSTensor

/-- A primitive MPS tensor has self-overlap converging to 1.

This is a direct application of `mpvOverlap_tendsto_one_of_transfer_spectralRadius_compl_lt_one`
from `PrimitiveOverlap.lean`, using the hypotheses recorded in the
`Kraus.HasComplementaryFixedPointGap` structure. -/
theorem _root_.Kraus.HasComplementaryFixedPointGap.overlap_tendsto_one {d D : ℕ} [NeZero D]
    {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : Kraus.HasComplementaryFixedPointGap A ρ) :
    Tendsto (fun N ↦ mpvOverlap (α := Fin d) A A N) atTop (nhds (1 : ℂ)) :=
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
    (hPrim : _root_.IsPrimitive (Kraus.transferMap (ι := Fin d) (n := Fin D) A)) :
    Tendsto (fun N ↦ mpvOverlap (α := Fin d) A A N) atTop (nhds (1 : ℂ)) := by
  classical
  obtain ⟨_, hP⟩ : Kraus.HasPrimitiveFixedPoint A :=
    Kraus.hasPrimitiveFixedPoint_of_peripheralPrimitive_of_irreducible A hIrr hNorm hPrim
  simpa only using Kraus.HasComplementaryFixedPointGap.overlap_tendsto_one hP

end MPSTensor

end

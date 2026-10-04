/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.MatrixSqrt
import QICLean.Analysis.SpectralRadiusPowerDecay
import QICLean.Channel.Peripheral.IrreducibleChannel
import QICLean.Channel.Primitive
import QICLean.Kraus.InvariantProjection
import TNLean.Algebra.MatrixCyclicPathSum
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.MPS.Core.BlockingTransfer
import TNLean.MPS.Core.CanonicalNormalization
import TNLean.MPS.Core.CyclicTrace
import TNLean.MPS.RFP.Defs

import TNLean.MPS.Preparation.FixedPointPairState

/-!
# Convergence to the fixed-point transfer map

The concrete fixed-point tensor, its cyclic pair state and their algebraic identities are
re-exported from `TNLean.MPS.Preparation.FixedPointPairState`. This module adds the spectral
convergence statements used in the log-depth preparation of arXiv:2307.01696.

The blocked transfer map converges to the rank-one map `X ↦ Tr(X) σ` when the complementary
map has spectral radius below one. For a normal left-canonical tensor, the peripheral gap
supplies that hypothesis. These are the transfer-map limits in eqs. `eq:Ek_decomp` and
`eq:B_TM`; the positive polar-factor limit is proved in
`TNLean.MPS.Preparation.ApproximatingState`.

The original import path retains the concrete pair-state API as well as these convergence
results.
-/

open scoped Kronecker Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.Operator
open Matrix Finset Filter

attribute [local instance 1001]
  ContinuousLinearMap.toNormedAddCommGroup
  ContinuousLinearMap.toNormedSpace
  ContinuousLinearMap.toNormedRing
  ContinuousLinearMap.toNormedAlgebra

namespace MPSTensor

variable {d D : ℕ}

/-! ## Convergence of the blocked transfer map -/

/-- The blocked transfer map converges to the transfer map of `P_∞`, from the
decomposition `E_A = |ρ⟩⟨1| + R` of arXiv:2307.01696, eq. `eq:Ek_decomp`: here `A`
is left canonical, `σ` is a unit-trace fixed point, and `R = E_A - E_{P_∞}` has
spectral radius less than one. This is the limit `E_B = E_A^q → E_{P_∞}` of
eq. `eq:B_TM`, for the blocked tensor `B` of eq. `eq:B`. -/
theorem tendsto_transferMap_blockTensor_of_spectralRadius_lt_one
    (A : MPSTensor d D) (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosSemidef) (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ)
    (hR : spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
        (Kraus.transferMap A - Kraus.transferMap (fixedPointTensor σ))) < 1)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    Tendsto (fun q : ℕ => Kraus.transferMap (blockTensor A q) X) atTop
      (nhds (Kraus.transferMap (fixedPointTensor σ) X)) := by
  have htr' : σ.trace ≠ 0 := by simp [htr]
  set E := Kraus.transferMap A
  set P := fixedPointProj σ htr'
  have hEP : Kraus.transferMap (fixedPointTensor σ) = P :=
    transferMap_fixedPointTensor hσ htr
  rw [hEP] at hR ⊢
  have hpow := pow_tendsto_zero_of_spectralRadius_lt_one _ hR
  have happ : Tendsto (fun q : ℕ => ((E - P) ^ q) X) atTop (nhds 0) := by
    have := ((ContinuousLinearMap.apply ℂ _ X).continuous.tendsto 0).comp hpow
    convert this using 1
    · funext q
      simp only [Function.comp_apply, ContinuousLinearMap.apply_apply, ← map_pow]
      rfl
    · simp only [map_zero]
      rfl
  have hTP : IsTracePreservingMap E := Kraus.isTracePreservingMap_mapLM_of_isTP A hA
  have hlim : Tendsto (fun q : ℕ => P X + ((E - P) ^ q) X) atTop (nhds (P X)) := by
    simpa using (tendsto_const_nhds (x := P X)).add happ
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with q hq
  rw [transferMap_blockTensor_apply,
    pow_eq_fixedPointProj_add_compl_pow E htr' hTP hfix hq]
  rfl

/-- For a normal tensor in the gauge of arXiv:2307.01696, eq. `eq:Ek_decomp`, the
blocked transfer map converges to the transfer map `|ρ⟩⟨1|` of `P_∞`: the limit
of eq. `eq:B_TM`. Normality is the source's definition after
eq. `eq:transfer_matrix`: the letters have no nontrivial common invariant
subspace, and `1` is the only eigenvalue of `E_A` of modulus one.

Normality is taken as `MPSTensor.IsNormalTensor`; the proof uses its fields
`no_invariant_proj` and `primitive_transfer`. Its remaining field `spectral_radius_one` adds
nothing to the source's hypotheses here: in the left-canonical gauge `hA` the transfer map is a
channel, so a caller holding only the source's two conditions obtains `IsNormalTensor A` from
`MPSTensor.isNormalTensor_of_isIrreducibleFamily_leftCanonical`. -/
theorem tendsto_transferMap_blockTensor_of_isPrimitive
    (A : MPSTensor d D) (hN : IsNormalTensor A) (hA : IsLeftCanonical A)
    {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef) (htr : σ.trace = 1)
    (hfix : Kraus.transferMap A σ = σ) (X : Matrix (Fin D) (Fin D) ℂ) :
    Tendsto (fun q : ℕ => Kraus.transferMap (blockTensor A q) X) atTop
      (nhds (Kraus.transferMap (fixedPointTensor σ) X)) := by
  have : NeZero D := ⟨by rintro rfl; simp at htr⟩
  obtain ⟨htr', hgap⟩ :=
    spectralRadius_compl_lt_one_of_primitive_fixedPoint_of_irreducible_channel
      (Kraus.transferMap A) (Kraus.isChannel_mapLM A hA)
      (Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily A hN.no_invariant_proj)
      hN.primitive_transfer σ hσ.posSemidef
      (by rintro rfl; simp at htr) hfix
  refine tendsto_transferMap_blockTensor_of_spectralRadius_lt_one A hA hσ.posSemidef htr hfix
    ?_ X
  rwa [transferMap_fixedPointTensor hσ.posSemidef htr]

end MPSTensor

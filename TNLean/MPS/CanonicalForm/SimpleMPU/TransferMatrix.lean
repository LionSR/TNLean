/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.Peripheral.Spectrum.Spectrum
import TNLean.MPS.Operator.Unitary.Basic
import TNLean.MPS.CanonicalForm.VerticalForm.Purity
import TNLean.MPS.Transfer.Spectrum.MPVOverlapTrace
import TNLean.MPS.CanonicalForm.SimpleMPU.PhysicalRelabelling

/-!
# Normalized transfer matrix of a Matrix Product Unitary

This file defines the paper-normalized tensor `U / sqrt d` on the pair alphabet of an MPO
and proves the transfer-matrix trace identity used in Proposition `prop:normal-tensor` of
Cirac--Perez-Garcia--Schuch--Verstraete.

## Main definitions

* `MPOTensor.normalizedFlattening` — the normalized tensor `U / sqrt d` on the pair alphabet.

## Main results

* `MPOTensor.sqrt_smul_normalizedFlattening` — multiplying back by `sqrt d` recovers `U`.
* `MPOTensor.mpvOverlap_normalizedFlattening_self` — its self-overlap scaling law.
* `MPOTensor.IsMPU.trace_transferMatrix_normalizedFlattening_pow_eq_one` — for every `N > 1`,
  the trace of the `N`-th power of its transfer matrix is one.
* `MPOTensor.IsMPU.normalizedFlattening_nonzero_spectrum` — the nonzero transfer-matrix
  spectrum of the normalized flattening is `{1}`.
* `MPOTensor.IsMPU.normalizedFlattening_charpoly` — its exact characteristic polynomial is
  `X ^ (D * D - 1) * (X - 1)`.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, "Matrix Product Unitaries: Structure,
  Symmetries, and Topological Invariants", Proposition `prop:normal-tensor`, lines 344--354.
-/

open scoped Matrix BigOperators
open Polynomial

namespace MPOTensor

variable {d D : ℕ}

/-- The paper-normalized tensor `U / sqrt d` of an MPO tensor, on the pair alphabet.

Source: Cirac--Perez-Garcia--Schuch--Verstraete, equation `eq:transfer-op`,
lines 336--340. -/
noncomputable def normalizedFlattening (U : MPOTensor d D) : MPOTensor d D :=
  fun ij => ((Real.sqrt d : ℂ)⁻¹) • U ij

/-- Multiplying the normalized tensor back by `sqrt d` gives `U`. -/
theorem sqrt_smul_normalizedFlattening [NeZero d] (U : MPOTensor d D) :
    (fun ij ↦ (Real.sqrt d : ℂ) • U.normalizedFlattening ij) = U := by
  have hc : (Real.sqrt d : ℂ) ≠ 0 := by
    have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    exact_mod_cast (Real.sqrt_pos.mpr hd).ne'
  funext ij
  simp only [normalizedFlattening, smul_smul, mul_inv_cancel₀ hc, one_smul]

/-- The length-`N` self-overlap of the normalized tensor is `d⁻ᴺ` times the raw
self-overlap. The physical dimension is explicitly nonzero so that division by `sqrt d`
has the paper's intended meaning.

Source: Cirac--Perez-Garcia--Schuch--Verstraete, Proposition `prop:normal-tensor`,
lines 344--354. -/
theorem mpvOverlap_normalizedFlattening_self [NeZero d]
    (U : MPOTensor d D) (N : ℕ) :
    MPTensor.mpvOverlap U.normalizedFlattening U.normalizedFlattening N =
      ((d : ℂ)⁻¹) ^ N * MPTensor.mpvOverlap U U N := by
  change MPTensor.mpvOverlap (fun ij ↦ ((Real.sqrt d : ℂ)⁻¹) • U ij)
    (fun ij ↦ ((Real.sqrt d : ℂ)⁻¹) • U ij) N = _
  rw [MPTensor.mpvOverlap_smul_self]
  congr 2
  have hd : (0 : ℝ) < d := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  simp only [RCLike.star_def, map_inv₀, Complex.conj_ofReal]
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt hd.le]
  simp

/-- For an MPU and every system size `N > 1`, the transfer matrix of the normalized
flattening satisfies `trace(E^N) = 1`.

The restriction `N > 1` is exact: `IsMPU` asserts unitarity only at those lengths, so no
length-one identity is claimed. Both physical and bond dimensions are explicitly nonzero.

Source: Cirac--Perez-Garcia--Schuch--Verstraete, Proposition `prop:normal-tensor`,
lines 344--354, using equation `UisUnitary`, lines 327--335. -/
theorem IsMPU.trace_transferMatrix_normalizedFlattening_pow_eq_one
    [NeZero d] [NeZero D] {U : MPOTensor d D} (hU : IsMPU U)
    {N : ℕ} (hN : 1 < N) :
    Matrix.trace (transferMatrix (Kraus.transferMap U.normalizedFlattening) ^ N) = 1 := by
  have h := MPSTensor.trace_transferMatrix_transferMap_pow_eq_mpvOverlap
    (Kraus.reindexPhysical finProdFinEquiv.symm U.normalizedFlattening) N
  rw [Kraus.transferMap_reindexPhysical_equiv, MPTensor.mpvOverlap_reindexPhysical] at h
  rw [h, mpvOverlap_normalizedFlattening_self, mpvOverlap_self,
    hU.mpo_mul_conjTranspose_mpo hN, Matrix.trace_one]
  rw [Fintype.card_pi_const]
  push_cast
  rw [← mul_pow]
  simp [NeZero.ne d]

/-- The transfer matrix of the normalized flattening of an MPU has nonzero set spectrum
exactly `{1}`.

This is the set-spectrum conclusion in Cirac--Perez-Garcia--Schuch--Verstraete,
Proposition `prop:normal-tensor`, lines 349--354.

**Scope restriction (set spectrum only):** Set equality alone does not assert
algebraic multiplicity. See `docs/paper-gaps/cpsv17_transfer_trace_power.tex`.
The exact conclusion is `MPOTensor.IsMPU.normalizedFlattening_charpoly`. -/
theorem IsMPU.normalizedFlattening_nonzero_spectrum
    [NeZero d] [NeZero D] {U : MPOTensor d D} (hU : IsMPU U) :
    spectrum ℂ (transferMatrix (Kraus.transferMap U.normalizedFlattening)) \ {0} = {1} :=
  Matrix.spectrum_diff_zero_eq_singleton_of_forall_trace_pow_eq_one_of_one_lt _
    (fun _ hN => hU.trace_transferMatrix_normalizedFlattening_pow_eq_one hN)

/-- The transfer matrix of the normalized flattening of an MPU has characteristic
polynomial `X ^ (D * D - 1) * (X - 1)`. Hence its sole nonzero eigenvalue is
`1`, with algebraic multiplicity one.

Source: Cirac--Perez-Garcia--Schuch--Verstraete, Proposition
`prop:normal-tensor`, lines 349--354. -/
theorem IsMPU.normalizedFlattening_charpoly
    [NeZero d] [NeZero D] {U : MPOTensor d D} (hU : IsMPU U) :
    (transferMatrix (Kraus.transferMap U.normalizedFlattening)).charpoly =
      X ^ (D * D - 1) * (X - 1) := by
  simpa [Fintype.card_prod, Fintype.card_fin] using
    Matrix.charpoly_eq_X_pow_pred_mul_X_sub_one_of_forall_trace_pow_eq_one_of_one_lt
      (transferMatrix (Kraus.transferMap U.normalizedFlattening))
      (fun _ hN => hU.trace_transferMatrix_normalizedFlattening_pow_eq_one hN)

end MPOTensor

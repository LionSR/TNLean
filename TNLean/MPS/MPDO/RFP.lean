/- 
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.ZCL

/-!
# General MPDO renormalization fixed point

This file states consequences of the current mixed-state RFP definition for
MPO tensors, following the transfer-map aspect of arXiv:1606.00608,
Definition 4.1.

The full definition in the paper is phrased using trace-preserving completely
positive blocking and unblocking maps. In this first pass `MPOTensor.IsRFP`
states the transfer-map idempotence condition, which is the part already
supported by the current formalization.

## Main results

* `MPOTensor.isRFP_iff_isZCL`: this current RFP condition coincides with
  `MPOTensor.IsZCL`.

## References

* [CPGSV17] arXiv:1606.00608, §4.1
-/

open scoped Matrix

namespace MPOTensor

variable {d D : ℕ}

/-- In the current development, the current mixed-state RFP condition is
definitionally the same as MPO ZCL. -/
theorem isRFP_iff_isZCL (M : MPOTensor d D) : IsRFP M ↔ IsZCL M :=
  Iff.rfl

/-- The current mixed-state RFP condition implies MPO ZCL. -/
theorem IsRFP.isZCL {M : MPOTensor d D} (h : IsRFP M) : IsZCL M :=
  h

/-- The current mixed-state RFP condition is equivalent to the pure-state
RFP condition for the doubled-index MPS tensor. -/
theorem isRFP_iff_toMPSTensor_isRFP (M : MPOTensor d D) :
    IsRFP M ↔ MPSTensor.IsRFP (M.toMPSTensor) := by
  simpa [IsRFP, MPOTensor.IsZCL] using isZCL_iff_toMPSTensor_isRFP M

end MPOTensor

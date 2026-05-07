/- 
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.ZCL

/-!
# General MPDO renormalization fixed point

This file states relations between the MPO transfer-map idempotence condition
(`MPOTensor.IsRFP`) and MPO zero correlation length (`MPOTensor.IsZCL`),
following arXiv:1606.00608, Definition 4.1.

## Main results

* `MPOTensor.isRFP_iff_isZCL`: `IsRFP M ↔ IsZCL M`.
* `MPOTensor.isRFP_iff_toMPSTensor_isRFP`: equivalence with the doubled-index
  MPS RFP condition.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608, Section 4.1
-/

open scoped Matrix

namespace MPOTensor

variable {d D : ℕ}

/-- `IsRFP M` is definitionally `IsZCL M`. -/
theorem isRFP_iff_isZCL (M : MPOTensor d D) : IsRFP M ↔ IsZCL M :=
  Iff.rfl

/-- `IsRFP M` implies `IsZCL M`. -/
theorem IsRFP.isZCL {M : MPOTensor d D} (h : IsRFP M) : IsZCL M :=
  h

/-- `IsRFP M` is equivalent to the pure-state RFP condition for the
doubled-index MPS tensor. -/
theorem isRFP_iff_toMPSTensor_isRFP (M : MPOTensor d D) :
    IsRFP M ↔ MPSTensor.IsRFP (M.toMPSTensor) := by
  simpa [IsRFP, MPOTensor.IsZCL] using isZCL_iff_toMPSTensor_isRFP M

end MPOTensor

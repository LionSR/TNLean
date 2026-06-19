/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.ZCL

/-!
# MPDO transfer-map idempotence and zero correlation length

This file relates the MPO transfer-map idempotence condition (`MPOTensor.IsRFP`)
and MPO zero correlation length (`MPOTensor.IsZCL`); the two are definitionally
equal here.

Note that `IsRFP` is the idempotence / zero-correlation-length condition, not the
paper's renormalization-fixed-point Definition 4.1 (paper label RFPMixedTS, the
existence of two trace-preserving CP maps), which is an a priori different notion
for general MPDO; see the faithfulness note on `MPOTensor.IsRFP`. Definition 4.1
is stated as `MPOTensor.IsRFPViaTS`; the theorem deriving idempotence from it is
future work (#826, #237).

## Main results

* `MPOTensor.isRFP_iff_isZCL`: `IsRFP M ↔ IsZCL M`.
* `MPOTensor.isRFP_iff_toMPSTensor_isRFP`: equivalence with the doubled-index
  MPS RFP condition.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Definition 4.2 (ZCL, line 735) and Definition 4.1 (paper label RFPMixedTS,
  line 657)
-/

open scoped Matrix

namespace MPOTensor

variable {d D : ℕ}

/-- `IsRFP M` is definitionally `IsZCL M`. -/
theorem isRFP_iff_isZCL (M : MPOTensor d D) : IsRFP M ↔ IsZCL M :=
  Iff.rfl

/-- `IsRFP M` is equivalent to the pure-state RFP condition for the
doubled-index MPS tensor. -/
theorem isRFP_iff_toMPSTensor_isRFP (M : MPOTensor d D) :
    IsRFP M ↔ MPSTensor.IsRFP (M.toMPSTensor) := by
  simpa [IsRFP, MPOTensor.IsZCL] using isZCL_iff_toMPSTensor_isRFP M

end MPOTensor

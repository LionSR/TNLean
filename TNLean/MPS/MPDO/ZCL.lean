/- 
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.Defs
import TNLean.MPS.RFP.Defs

/-!
# Zero correlation length for MPO tensors

Definitions of zero-correlation-length conditions for mixed-state tensor
networks, following arXiv:1606.00608, Definition 4.2.

## Main definitions

* `MPOTensor.IsZCL`: the MPO transfer map is idempotent.
* `MPOTensor.isZCL_iff_toMPSTensor_isRFP`: this condition is equivalent to the
  pure-state RFP condition for the doubled-index MPS tensor.

## References

* [CPGSV17] arXiv:1606.00608, §4.2
-/

open scoped Matrix

namespace MPOTensor

variable {d D : ℕ}

/-- An MPO tensor has **zero correlation length** when its transfer map is
idempotent:
`E_M ∘ E_M = E_M`.

This is the mixed-state analogue of `MPSTensor.IsRFP`. See
arXiv:1606.00608, Definition 4.2. -/
def IsZCL (M : MPOTensor d D) : Prop :=
  transferMap M ∘ₗ transferMap M = transferMap M

/-- ZCL for an MPO tensor is equivalent to the pure-state RFP condition for
the doubled-index MPS tensor `M.toMPSTensor`. Both statements assert
idempotence of the same transfer map. -/
theorem isZCL_iff_toMPSTensor_isRFP (M : MPOTensor d D) :
    IsZCL M ↔ MPSTensor.IsRFP (M.toMPSTensor) := by
  simp [IsZCL, MPSTensor.IsRFP]

end MPOTensor

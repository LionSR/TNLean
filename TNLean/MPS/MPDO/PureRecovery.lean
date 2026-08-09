/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.ZCL
import TNLean.MPS.RFP.ZeroCorrelationLength

/-!
# Pure-state recovery inside the MPO formalism

This file studies the diagonal embedding of a pure MPS tensor into the MPO
formalism and compares doubled-index transfer-map idempotence with the usual
pure-state `IsTransferIdempotent` and `IsZCL` conditions.
-/

namespace MPSTensor

open MPOTensor

variable {d D : ℕ}

/-- Embed a pure MPS tensor as a diagonal MPO with trivial bra structure:
`M^{ij} = δ_{ij} A^i`. -/
def toMPOTensor (A : MPSTensor d D) : MPOTensor d D :=
  fun i j => if i = j then A i else 0

@[simp] lemma toMPOTensor_apply_same (A : MPSTensor d D) (i : Fin d) :
    A.toMPOTensor i i = A i := by
  simp [toMPOTensor]

@[simp] lemma toMPOTensor_apply_ne (A : MPSTensor d D) {i j : Fin d}
    (hij : i ≠ j) :
    A.toMPOTensor i j = 0 := by
  simp [toMPOTensor, hij]

/-- The transfer map of the diagonal pure-state embedding is exactly the
original MPS transfer map. -/
@[simp] theorem toMPOTensor_transferMap (A : MPSTensor d D) :
    MPOTensor.transferMap A.toMPOTensor = transferMap A := by
  ext X
  rw [MPOTensor.transferMap_apply, transferMap_apply]
  simp [toMPOTensor]

/-- For a pure MPS viewed as a diagonal MPO, doubled-index transfer-map
idempotence is exactly the original pure-state transfer-map condition. -/
theorem toMPOTensor_isZCL_iff_isTransferIdempotent (A : MPSTensor d D) :
    MPOTensor.IsZCL A.toMPOTensor ↔ IsTransferIdempotent A := by
  rw [MPOTensor.IsZCL, IsTransferIdempotent, toMPOTensor_transferMap]

/-- For a pure MPS embedded as a diagonal MPO, doubled-index transfer-map
idempotence reduces to the pure-state zero-correlation-length condition via
`MPSTensor.zcl_iff_idempotent_transfer`. -/
theorem toMPOTensor_isZCL_iff_mps_isZCL (A : MPSTensor d D) :
    MPOTensor.IsZCL A.toMPOTensor ↔ MPSTensor.IsZCL A :=
  (toMPOTensor_isZCL_iff_isTransferIdempotent A).trans
    (zcl_iff_idempotent_transfer A).symm

end MPSTensor

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Operator.Defs
import TNLean.MPS.Operator.Unitary.Basic

/-!
# The bond-one identity matrix product unitary

The identity tensor generates the identity operator at every length and is a matrix product
unitary for every physical dimension.
-/

namespace MPOTensor

/-- The bond-one identity MPO tensor. -/
noncomputable def identityMPUTensor (d : ℕ) : MPOTensor d 1 := idTensor d

/-- The identity tensor generates the identity on every chain. -/
theorem mpo_identityMPUTensor (d N : ℕ) : mpo (identityMPUTensor d) N = 1 :=
  mpo_idTensor d N

/-- The identity tensor is an MPU. -/
theorem identityMPUTensor_isMPU (d : ℕ) : IsMPU (identityMPUTensor d) := by
  intro N _hN
  rw [mpo_identityMPUTensor, Matrix.mem_unitaryGroup_iff]
  simp

end MPOTensor

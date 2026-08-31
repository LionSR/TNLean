/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.SitewisePhysicalMatrix
import TNLean.MPS.MPU.Basic

/-!
# Matrix product unitaries under physical left actions

A unitary acting on the ket leg of every local MPO matrix preserves the matrix product unitary
property.
-/

open scoped Matrix

namespace MPOTensor

variable {d D : ℕ}

/-- Left multiplication by a one-site unitary preserves the MPU property. -/
theorem IsMPU.ketLeftMul {M : MPOTensor d D} (hM : IsMPU M)
    {P : Matrix (Fin d) (Fin d) ℂ}
    (hP : P ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    IsMPU (M.ketLeftMul P) := by
  intro N hN
  rw [mpo_ketLeftMul]
  apply (Matrix.unitaryGroup (Fin N → Fin d) ℂ).mul_mem
  · rw [Matrix.mem_unitaryGroup_iff']
    rw [Matrix.star_eq_conjTranspose, sitewisePhysicalMatrix_isometry P]
    rw [Matrix.mem_unitaryGroup_iff'] at hP
    simpa only [Matrix.star_eq_conjTranspose] using hP
  · exact hM.mpo_mem_unitaryGroup hN

end MPOTensor

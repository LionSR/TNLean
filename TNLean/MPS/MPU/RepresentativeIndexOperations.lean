/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.RepresentativeIndex

/-!
# Blocking and adjunction of the representative MPU index

The index of an arbitrary positive-dimensional matrix product unitary is
defined through a reduced canonical-form-II representative. Positive physical
blocking preserves this index, and physical adjunction reverses its sign.
Both statements descend from the corresponding canonical-form-II identities
through equality of the positive-length periodic operator families.

**Scope restriction (representative index):** No equality of the unreduced
tensor's own source-cut ranks with those of its reduced representative is
asserted. See `docs/paper-gaps/mpu_canonical_form_full_support.tex`.

## References

* CPSV17, arXiv:1703.09188, Proposition `index-well-defined`, lines 690–704.
* CPSV17, arXiv:1703.09188, physical-adjoint index discussion, lines 1196–1207.
-/

namespace MPOTensor

/-- Positive physical blocking preserves the representative-defined index of
every positive-dimensional MPU. CPSV17, Proposition IV.2, lines 690–704. -/
theorem IsMPU.index_blockTensor
    {d D : ℕ} [NeZero d] [NeZero D] {U : MPOTensor d D}
    (hU : IsMPU U) (p : ℕ) (hp : 0 < p) :
    (hU.blockTensor p hp).index = hU.index := by
  let : NeZero (MPSTensor.blockPhysDim d p) := ⟨by
    rw [MPSTensor.blockPhysDim_eq_pow]
    exact pow_ne_zero p (NeZero.ne d)⟩
  obtain ⟨Dred, _, Ured, hred, _, hMpo⟩ :=
    hU.exists_reduced_cfii_representative
  calc
    (hU.blockTensor p hp).index = (hred.blockTensor p hp).index := by
      apply (hU.blockTensor p hp).index_eq_canonical_representative
      intro N hN
      rw [mpo_blockTensor_eq_reindex, mpo_blockTensor_eq_reindex]
      rw [hMpo (N * p) (Nat.mul_pos hN hp)]
    _ = hred.index := hred.index_blockTensor p hp
    _ = hU.index := (hU.index_eq_canonical_representative hred hMpo).symm

/-- Physical adjunction reverses the representative-defined index of every
positive-dimensional MPU. CPSV17, lines 1196–1207. -/
theorem IsMPU.index_physicalAdjointTensor
    {d D : ℕ} [NeZero d] [NeZero D] {U : MPOTensor d D}
    (hU : IsMPU U) :
    hU.physicalAdjointTensor.index = -hU.index := by
  obtain ⟨Dred, _, Ured, hred, _, hMpo⟩ :=
    hU.exists_reduced_cfii_representative
  calc
    hU.physicalAdjointTensor.index = hred.physicalAdjointTensor.index := by
      apply hU.physicalAdjointTensor.index_eq_canonical_representative
      intro N hN
      ext σ τ
      rw [mpo_physicalAdjointTensor, mpo_physicalAdjointTensor]
      rw [hMpo N hN]
    _ = -hred.index := hred.index_physicalAdjointTensor
    _ = -hU.index := congrArg Neg.neg (hU.index_eq_canonical_representative hred hMpo).symm

end MPOTensor

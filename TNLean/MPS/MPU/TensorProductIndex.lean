/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.IdentityIndex
import TNLean.MPS.MPU.TensorProductCanonicalForm

/-!
# Tensor-product additivity of the MPU index

For two tensors in canonical form II, the index of their independent tensor
product is the sum of their indices. Choose a common positive simple blocking
of the two factors and their product. The two source-cut ranks multiply, and
the logarithmic formula gives additivity. Tensoring with a finite-dimensional
identity tensor consequently leaves the index unchanged.

**Scope restriction (canonical representatives):** both factors are already
in canonical form II. No identification of indices across support reduction
is asserted. See `docs/paper-gaps/mpu_canonical_form_full_support.tex`.

## References

* Cirac--Pérez-García--Schuch--Verstraete, arXiv:1703.09188,
  Theorem `IndexTh` (ii), lines 824--845.
* The finite identity factor in `def:equivalent-tensors`, lines 706--720.
-/

namespace MPOTensor

variable {d D e E : ℕ} {U : MPOTensor d D} {V : MPOTensor e E}

/-- The base-two index is additive under independent tensor products of
canonical-form-II representatives. The common simple blocking and its rank
products are derived, not supplied.
Source: arXiv:1703.09188, Theorem `IndexTh` (ii), lines 824--845. -/
theorem IsMPUCanonicalFormII.index_tensorProduct
    (hU : IsMPUCanonicalFormII U) (hV : IsMPUCanonicalFormII V) :
    (hU.tensorProduct hV).index = hU.index + hV.index := by
  obtain ⟨p, hp, _, hSp, _⟩ := hU.exists_sourceV_blockTensor_isIsometry
  obtain ⟨⟨q, hq, _, hSq, _⟩, ⟨t, ht, _, hSt, _⟩⟩ :=
    And.intro hV.exists_sourceV_blockTensor_isIsometry
      (hU.tensorProduct hV).exists_sourceV_blockTensor_isIsometry
  have hcommon : 0 < p + q + t ∧
      IsMPUSimple (MPOTensor.blockTensor U (p + q + t)) ∧
      IsMPUSimple (MPOTensor.blockTensor V (p + q + t)) ∧
      IsMPUSimple (MPOTensor.blockTensor (MPOTensor.tensorProduct U V) (p + q + t)) :=
    ⟨by omega,
      hU.isMPU.blockTensor_isMPUSimple_of_le hp (by omega) hSp,
      hV.isMPU.blockTensor_isMPUSimple_of_le hq (by omega) hSq,
      (hU.tensorProduct hV).isMPU.blockTensor_isMPUSimple_of_le ht (by omega) hSt⟩
  exact let hu := hU.sourceRanks_blockTensor_pos hcommon.1 hcommon.2.1
    let hv := hV.sourceRanks_blockTensor_pos hcommon.1 hcommon.2.2.1
    let hw := (hU.tensorProduct hV).sourceRanks_blockTensor_pos hcommon.1 hcommon.2.2.2
    ((hU.tensorProduct hV).sourceIndexValue_eq_index
      hcommon.1 hcommon.2.2.2 hw.1 hw.2).symm.trans
      ((sourceIndexValue_eq_add_of_common_rank_product
        (MPOTensor.blockTensor U (p + q + t)) (MPOTensor.blockTensor V (p + q + t))
        (MPOTensor.blockTensor (MPOTensor.tensorProduct U V) (p + q + t))
        1 Nat.one_pos hu.1 hu.2 hv.1 hv.2 hw.1 hw.2
        (by simp only [blockTensor_tensorProduct, rightRank_reindexPhysical,
          rightRank_tensorProduct, one_mul])
        (by simp only [blockTensor_tensorProduct, leftRank_reindexPhysical,
          leftRank_tensorProduct, one_mul])).trans
        (congrArg₂ (· + ·)
          (hU.sourceIndexValue_eq_index hcommon.1 hcommon.2.1 hu.1 hu.2)
          (hV.sourceIndexValue_eq_index hcommon.1 hcommon.2.2.1 hv.1 hv.2)))

/-- Adding a finite identity factor does not change the index.
Source: arXiv:1703.09188, `def:equivalent-tensors`, lines 706--720, and
Theorem `IndexTh` (ii), lines 824--845. -/
theorem IsMPUCanonicalFormII.index_tensorProduct_identityMPUTensor
    (hU : IsMPUCanonicalFormII U) (n : ℕ) [NeZero n] :
    (hU.tensorProduct (identityMPUTensorCanonicalFormII n)).index = hU.index := by
  rw [IsMPUCanonicalFormII.index_tensorProduct, identityMPUTensor_index, add_zero]

end MPOTensor

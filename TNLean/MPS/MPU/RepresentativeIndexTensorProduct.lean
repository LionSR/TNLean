/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.RepresentativeIndex
import TNLean.MPS.MPU.TensorProductIndex

/-!
# Tensor products and the representative MPU index

The index of an arbitrary positive-dimensional matrix product unitary is
defined using a reduced canonical-form-II representative. The periodic
operator of an independent tensor product is the reindexed Kronecker product
of the two periodic operators. Consequently the tensor product of reduced
representatives represents the product family, and canonical index
additivity descends to arbitrary positive-dimensional MPUs. The bond-one
identity tensor has index zero, so it may be adjoined as an independent
physical factor without changing the index.

**Scope restriction (representative index):** These statements concern the
index defined through reduced canonical representatives. They do not assert
that rectangular reduction preserves the raw source-cut ranks of the
unreduced tensor. See `docs/paper-gaps/mpu_canonical_form_full_support.tex`.

## References

* CPSV17, arXiv:1703.09188, Theorem `IndexTh` (ii), lines 824–845.
* CPSV17, arXiv:1703.09188, finite identity factors in
  Definition `def:equivalent-tensors`, lines 706–720.
-/

namespace MPOTensor

/-- The representative index is additive under the independent tensor
product of positive-dimensional MPUs. CPSV17, Theorem `IndexTh` (ii),
lines 824–845. -/
theorem IsMPU.index_tensorProduct
    {d D e E : ℕ} [NeZero d] [NeZero D] [NeZero e] [NeZero E]
    {U : MPOTensor d D} {V : MPOTensor e E}
    (hU : IsMPU U) (hV : IsMPU V) :
    (hU.tensorProduct hV).index = hU.index + hV.index := by
  let : NeZero (d * e) := ⟨mul_ne_zero (NeZero.ne d) (NeZero.ne e)⟩
  let : NeZero (D * E) := ⟨mul_ne_zero (NeZero.ne D) (NeZero.ne E)⟩
  obtain ⟨DredU, _, Ured, hredU, _, hMpoU⟩ :=
    hU.exists_reduced_cfii_representative
  obtain ⟨DredV, _, Vred, hredV, _, hMpoV⟩ :=
    hV.exists_reduced_cfii_representative
  calc
    (hU.tensorProduct hV).index = (hredU.tensorProduct hredV).index := by
      apply (hU.tensorProduct hV).index_eq_canonical_representative
      intro N hN
      rw [mpo_tensorProduct, mpo_tensorProduct, hMpoU N hN, hMpoV N hN]
    _ = hredU.index + hredV.index := hredU.index_tensorProduct hredV
    _ = hU.index + hV.index := by
      rw [← hU.index_eq_canonical_representative hredU hMpoU,
        ← hV.index_eq_canonical_representative hredV hMpoV]

/-- The bond-one identity tensor has representative index zero. CPSV17,
Definition IV.1 and Proposition IV.2, lines 681–704. -/
theorem IsMPU.index_identityMPUTensor (n : ℕ) [NeZero n] :
    (identityMPUTensor_isMPU n).index = 0 := by
  rw [(identityMPUTensor_isMPU n).index_eq_canonical_representative
    (identityMPUTensorCanonicalFormII n) (by intro N hN; rfl)]
  exact identityMPUTensor_index n

/-- Tensoring a positive-dimensional MPU with a bond-one identity tensor
does not change its representative index. CPSV17, Definition
`def:equivalent-tensors`, lines 706–720, and Theorem `IndexTh` (ii),
lines 824–845. -/
theorem IsMPU.index_tensorProduct_identityMPUTensor
    {d D : ℕ} [NeZero d] [NeZero D] {U : MPOTensor d D}
    (hU : IsMPU U) (n : ℕ) [NeZero n] :
    (hU.tensorProduct (identityMPUTensor_isMPU n)).index = hU.index := by
  calc
    (hU.tensorProduct (identityMPUTensor_isMPU n)).index =
        hU.index + (identityMPUTensor_isMPU n).index :=
      hU.index_tensorProduct (identityMPUTensor_isMPU n)
    _ = hU.index + 0 := congrArg (hU.index + ·) (IsMPU.index_identityMPUTensor n)
    _ = hU.index := add_zero _

end MPOTensor

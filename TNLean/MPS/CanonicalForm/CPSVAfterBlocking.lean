/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.MPS.CanonicalForm.SectorComparison.CommonSectorTransport

/-!
# CPSV canonical-form representative after blocking

This module constructs the canonical-form representative stated after the
canonical-form definition in Cirac--Pérez-García--Schuch--Verstraete,
arXiv:1606.00608, lines 249--251.

## Main statement

* `exists_cpsvCanonicalForm_representative_after_blocking` gives, after a
  positive blocking length, a tensor in literal CPSV canonical form with the same
  positive-length MPV family as the blocked input tensor.

## References

* [Cirac--Pérez-García--Schuch--Verstraete, arXiv:1606.00608, Section 2.3]

## Tags

matrix product states, canonical form, blocking, normal tensor
-/

open scoped BigOperators

namespace MPSTensor

/-- After a positive blocking length, every tensor has a possibly different
representative in literal CPSV canonical form which generates the same
positive-length MPV family.

The representative is the weighted direct sum of the primitive irreducible
left-canonical blocks. It need not equal the blocked input tensor in the
input tensor's original bond coordinates.

Source: arXiv:1606.00608, lines 214--251, especially eqs. `II_Aiplusk1` and
`II_CF1` and the proposition at lines 249--251. -/
theorem exists_cpsvCanonicalForm_representative_after_blocking
    (A : MPSTensor d D) :
    ∃ p : ℕ, 0 < p ∧
      ∃ D' : ℕ, ∃ B : MPSTensor (blockPhysDim d p) D',
        IsCPSVCanonicalForm B ∧
        SameMPV₂Pos (blockTensor A p) B := by
  have hRefl : SameMPV₂Pos A A := by
    intro N _hN σ
    rfl
  obtain ⟨p, hp, rA, dimA, μA, blocksA, rB, dimB, μB, blocksB,
      hABlocks, _hBBlocks, _hBlocksAgree, _hμA, _hμB, hLeftA, _hLeftB,
      hPrimitiveA, _hPrimitiveB, hIrreducibleA, _hIrreducibleB,
      hDimA, _hDimB⟩ :=
    unconditional_commonPrimitiveIrreducibleBlocks A A hRefl
  let B : MPSTensor (blockPhysDim d p) (∑ k : Fin rA, dimA k) :=
    toTensorFromBlocks (d := blockPhysDim d p) μA blocksA
  have hNormalA : ∀ k, IsNormalTensor (blocksA k) := by
    intro k
    letI : NeZero (dimA k) := ⟨Nat.ne_of_gt (hDimA k)⟩
    exact isNormalTensor_of_isNormal_leftCanonical (blocksA k)
      (isNormal_of_tp_primitive_irreducible (blocksA k)
        (hLeftA k) (hPrimitiveA k) (hIrreducibleA k))
      (hLeftA k)
  refine ⟨p, hp, ∑ k : Fin rA, dimA k, B, ?_, ?_⟩
  · exact (CPSVCanonicalFormData.ofBlocks hDimA μA blocksA hNormalA).isCPSVCanonicalForm
  · exact hABlocks

end MPSTensor

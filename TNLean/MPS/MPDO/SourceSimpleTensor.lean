/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.BNTTransport
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.MPS.MPDO.SimpleTensor

/-!
# Normalization-free Definition 4.7 simplicity

This module records the source-facing simplicity condition of arXiv:1606.00608,
Definition 4.7. After a positive physical blocking, the doubled-index tensor must
admit a CPSV basis of normal tensors, and the ket-against-bra contraction of every
basis element must be nonnilpotent. The interface requires every positive-length
generated MPO to be nonzero, but deliberately excludes the separate line-246
unit-weight normalization.

## Main result

* `MPOTensor.IsSourceSimple`: normalization-free Definition 4.7 simplicity.
* `MPOTensor.IsSimple.isSourceSimple`: normalized simplicity implies source
  simplicity under positive-length nonvanishing.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Definition 4.7, lines 815--822
-/

namespace MPOTensor

variable {d D : ℕ}

/-- **Normalization-free Definition 4.7 simplicity.** A tensor generating a
nonzero MPDO at every positive chain length is source-simple when, after some
positive physical blocking, its doubled-index tensor has a CPSV basis of normal
tensors and no basis element has nilpotent ket-against-bra contraction.

The positive-length nonzero condition records the source boundary that the
tensor generates a genuine density-operator family; in particular, null
periodic representations are not simple. The BNT witness uses
`MPSTensor.IsCPSVBasisOfNormalTensors`, rather than an arbitrary family of
canonical blocks. It does not impose the line-246 unit-weight normalization and
makes no claim that every positive blocking has such a witness.

Source: arXiv:1606.00608, Definition 4.7, lines 815--822. -/
def IsSourceSimple (M : MPOTensor d D) : Prop :=
  IsMPDO M ∧ (∀ N : ℕ, 0 < N → mpo M N ≠ 0) ∧
    ∃ L : ℕ, 0 < L ∧
      ∃ g : ℕ,
        ∃ blocks : (j : Fin g) →
            Σ D' : ℕ, MPSTensor
              (MPSTensor.blockPhysDim d L * MPSTensor.blockPhysDim d L) D',
          MPSTensor.IsCPSVBasisOfNormalTensors (blockTensor M L).toMPSTensor blocks ∧
            ∀ j, ¬ IsNilpotent
              (doubledPhysTraceTransfer (MPSTensor.blockPhysDim d L) (blocks j).2)

/-- Normalized simplicity implies source simplicity when the generated MPO is
nonzero at every positive length.

The extra nonvanishing hypothesis is necessary because `IsSimple` only asks
for a canonical form after one positive blocking. Its raw sector weights may
have phase cancellations at individual lengths, whereas `IsSourceSimple`
explicitly excludes every positive-length null generated operator.

The CPSV basis is the family of distinct normal representatives in the
normalized sector decomposition. Its spanning coefficients are the sector
power sums. The displayed global gauge preserves every matrix product vector,
so the basis transports to the blocked MPO tensor. The nonnilpotency clause is
unchanged because the representatives themselves are unchanged.

Source: arXiv:1606.00608, Definition 4.7, lines 815--822, together with the
normalized fixed-representative interface of lines 238--246. -/
theorem IsSimple.isSourceSimple {M : MPOTensor d D} (hM : IsSimple M)
    (hM_ne : ∀ N : ℕ, 0 < N → mpo M N ≠ 0) :
    IsSourceSimple M := by
  obtain ⟨hMPDO, L, hL, -, S, hCF, hNonNil, hTotal, X, hEq⟩ := hM
  refine ⟨hMPDO, hM_ne, L, hL, S.basisCount,
    fun j ↦ ⟨S.basisDim j, S.basis j⟩, ?_, hNonNil⟩
  subst hTotal
  have hBNT : MPSTensor.IsCPSVBasisOfNormalTensors S.toTensor
      (fun j ↦ ⟨S.basisDim j, S.basis j⟩) := by
    letI : ∀ j : Fin S.basisCount, NeZero (S.basisDim j) :=
      fun j ↦ ⟨(hCF.basis_dim_pos j).ne'⟩
    refine {
      blocks_normal := fun j ↦
        MPSTensor.isNormalTensor_of_isNormal_leftCanonical (S.basis j)
          (hCF.basis_isNormal j) (hCF.basis_left_canonical j)
      spans_mpv := fun N _ ↦ ⟨S.coeff N, fun σ ↦ S.mpv_toTensor_eq_sum_coeff σ⟩
      eventually_li := hCF.bnt_data }
  apply hBNT.of_sameMPV₂Pos
  intro N _ σ
  exact (MPSTensor.GaugeEquiv.sameMPV ⟨MPSTensor.globalGaugeOfBlocks X, hEq⟩ N σ)

end MPOTensor

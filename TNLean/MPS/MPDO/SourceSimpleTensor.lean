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
admit a CPSV basis of normal tensors, and the ket-against-bra contraction of
every basis element must be nonnilpotent. The source definition does not require
every positive-length generated MPO to be nonzero and excludes the separate
line-246 unit-weight normalization. The strengthened nonvanishing interface is
recorded separately.

## Main results

* `MPOTensor.IsSourceSimple`: normalization-free Definition 4.7 simplicity.
* `MPOTensor.IsNonvanishingSourceSimple`: source simplicity together with
  positive-length nonvanishing.
* `MPOTensor.IsSimple.isSourceSimple`: normalized simplicity implies source
  simplicity unconditionally.
* `MPOTensor.IsSimple.isNonvanishingSourceSimple`: normalized simplicity implies
  the strengthened interface under positive-length nonvanishing.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Definition 4.7, lines 815--822
-/

namespace MPOTensor

variable {d D : ℕ}

/-- **Normalization-free Definition 4.7 simplicity.** A tensor is source-simple
when it generates an MPDO and, after some positive physical blocking, its
doubled-index tensor has a CPSV basis of normal tensors whose ket-against-bra
contractions are all nonnilpotent.

The BNT witness uses `MPSTensor.IsCPSVBasisOfNormalTensors`, rather than an
arbitrary family of canonical blocks. The predicate does not impose either
positive-length nonvanishing or the line-246 unit-weight normalization and makes
no claim that every positive blocking has such a witness.

Source: arXiv:1606.00608, Definition 4.7, lines 815--822. -/
def IsSourceSimple (M : MPOTensor d D) : Prop :=
  IsMPDO M ∧ ∃ L : ℕ, 0 < L ∧
    ∃ g : ℕ,
      ∃ blocks : (j : Fin g) →
          Σ D' : ℕ, MPSTensor
            (MPSTensor.blockPhysDim d L * MPSTensor.blockPhysDim d L) D',
        MPSTensor.IsCPSVBasisOfNormalTensors (blockTensor M L).toMPSTensor blocks ∧
          ∀ j, ¬ IsNilpotent
            (doubledPhysTraceTransfer (MPSTensor.blockPhysDim d L) (blocks j).2)

/-- Source simplicity strengthened by nonvanishing of every positive-length
closed MPO. This condition is not part of CPSV16 Definition 4.7.

Source predicate: arXiv:1606.00608, Definition 4.7, lines 815--822. -/
def IsNonvanishingSourceSimple (M : MPOTensor d D) : Prop :=
  IsSourceSimple M ∧ ∀ N : ℕ, 0 < N → mpo M N ≠ 0

/-- The strengthened nonvanishing interface implies source simplicity. -/
theorem IsNonvanishingSourceSimple.isSourceSimple {M : MPOTensor d D}
    (hM : IsNonvanishingSourceSimple M) : IsSourceSimple M :=
  hM.1

/-- The strengthened interface supplies nonvanishing at every positive length. -/
theorem IsNonvanishingSourceSimple.mpo_ne_zero {M : MPOTensor d D}
    (hM : IsNonvanishingSourceSimple M) (N : ℕ) (hN : 0 < N) : mpo M N ≠ 0 :=
  hM.2 N hN

/-- Normalized simplicity implies source simplicity.

The CPSV basis is the family of distinct normal representatives in the
normalized sector decomposition. Its spanning coefficients are the sector
power sums. The global gauge preserves every matrix product vector, so the basis
transports to the blocked MPO tensor. The nonnilpotency clause is unchanged
because the representatives themselves are unchanged.

Source: arXiv:1606.00608, Definition 4.7, lines 815--822, together with the
normalized fixed-representative interface of lines 238--246. -/
theorem IsSimple.isSourceSimple {M : MPOTensor d D} (hM : IsSimple M) :
    IsSourceSimple M := by
  obtain ⟨hMPDO, L, hL, -, S, hCF, hNonNil, hTotal, X, hEq⟩ := hM
  refine ⟨hMPDO, L, hL, S.basisCount,
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

/-- Normalized simplicity implies the strengthened nonvanishing source interface
when every positive-length closed MPO is nonzero.

The nonvanishing assumption is additional to CPSV16 Definition 4.7. -/
theorem IsSimple.isNonvanishingSourceSimple {M : MPOTensor d D} (hM : IsSimple M)
    (hM_ne : ∀ N : ℕ, 0 < N → mpo M N ≠ 0) :
    IsNonvanishingSourceSimple M :=
  ⟨hM.isSourceSimple, hM_ne⟩

end MPOTensor

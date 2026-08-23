/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.BNTRefinement
import TNLean.MPS.MPDO.SimpleTensor

/-!
# Canonical-block reading of Definition 4.7 simplicity

This module records the canonical-block reading of arXiv:1606.00608,
Definition 4.7. After a positive physical blocking, the doubled-index tensor
must have a sector presentation by a basis of normal tensors, and the
ket-against-bra contraction of every representative must be nonnilpotent. The
definition does not require every positive-length generated MPO to be nonzero
and excludes the separate line-246 unit-weight normalization. The presentation
implies positive-length nontriviality; the stronger all-length nonvanishing
predicate is recorded separately.

## Main results

* `MPOTensor.IsSourceSimple`: the canonical-block reading of Definition 4.7.
* `MPOTensor.IsNonvanishingSourceSimple`: source simplicity together with
  positive-length nonvanishing.
* `MPOTensor.IsSimple.isSourceSimple`: normalized simplicity implies source
  simplicity unconditionally.
* `MPOTensor.IsSimple.isNonvanishingSourceSimple`: normalized simplicity implies
  the strengthened predicate under positive-length nonvanishing.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  canonical-block convention at lines 217--246 and Definition 4.7 at lines
  815--822
-/

namespace MPOTensor

variable {d D : ℕ}

/-- Nonnilpotency of all BNT representatives is independent of the chosen presentation.

The BNT uniqueness theorem matches representatives by permutation, equal bond
dimension, gauge, and phase.  Similarity, nonzero scalar multiplication, and the resulting
dimension identification preserve nilpotency of the physical-trace transfer.

Source: arXiv:1606.00608, Definition 4.7, lines 815--822, and Proposition 2.7,
lines 1135--1148. -/
theorem bnt_basis_not_isNilpotent_iff
    {D' p : ℕ} {A : MPSTensor (p * p) D'}
    {P Q : MPSTensor.SectorDecomposition (p * p)}
    (hP : MPSTensor.IsBNTSectorPresentation A P)
    (hQ : MPSTensor.IsBNTSectorPresentation A Q) :
    (∀ j, ¬ IsNilpotent (doubledPhysTraceTransfer p (P.basis j))) ↔
      ∀ k, ¬ IsNilpotent (doubledPhysTraceTransfer p (Q.basis k)) := by
  classical
  obtain ⟨e, hEquiv⟩ := hP.equiv_of_sameMPV₂Pos hQ (fun _ _ _ => rfl)
  constructor
  · intro hPNonNil k hQNil
    let j := e.symm k
    obtain ⟨hdim, hGauge⟩ := hEquiv j
    have hQNil' : IsNilpotent (doubledPhysTraceTransfer p (Q.basis (e j))) := by
      rw [e.apply_symm_apply]
      exact hQNil
    have hCastNil : IsNilpotent
        (doubledPhysTraceTransfer p
          (cast (congr_arg (MPSTensor (p * p)) hdim) (P.basis j))) :=
      (isNilpotent_doubledPhysTraceTransfer_iff_of_gaugePhaseEquiv
        hGauge.toGaugePhaseEquiv).mpr hQNil'
    exact hPNonNil j
      ((isNilpotent_doubledPhysTraceTransfer_cast_iff hdim (P.basis j)).mp hCastNil)
  · intro hQNonNil j hPNil
    obtain ⟨hdim, hGauge⟩ := hEquiv j
    have hCastNil : IsNilpotent
        (doubledPhysTraceTransfer p
          (cast (congr_arg (MPSTensor (p * p)) hdim) (P.basis j))) :=
      (isNilpotent_doubledPhysTraceTransfer_cast_iff hdim (P.basis j)).mpr hPNil
    exact hQNonNil (e j)
      ((isNilpotent_doubledPhysTraceTransfer_iff_of_gaugePhaseEquiv
        hGauge.toGaugePhaseEquiv).mp hCastNil)

/-- **Canonical-block reading of Definition 4.7 simplicity.** A tensor is source-simple
when it generates an MPDO and, after some positive physical blocking, its doubled-index
tensor has a sector presentation by a basis of normal tensors whose ket-against-bra
contractions are all nonnilpotent.

Every representative has a positive number of copies, every copy has nonzero weight, and
distinct representatives are eventually linearly independent.  Thus positive-length
nontriviality follows rather than being postulated.  The predicate excludes the separate
line-246 unit-weight normalization and makes no claim that every positive blocking has such
a witness.

Source: arXiv:1606.00608, canonical-block convention at lines 217--246 and
Definition 4.7, lines 815--822. -/
def IsSourceSimple (M : MPOTensor d D) : Prop :=
  IsMPDO M ∧
    ∃ L : ℕ, 0 < L ∧
      ∃ P : MPSTensor.SectorDecomposition
          (MPSTensor.blockPhysDim d L * MPSTensor.blockPhysDim d L),
        MPSTensor.IsBNTSectorPresentation
            (blockTensor M L).toMPSTensor P ∧
          ∀ j, ¬ IsNilpotent
            (doubledPhysTraceTransfer (MPSTensor.blockPhysDim d L) (P.basis j))

/-- Source simplicity strengthened by nonvanishing of every positive-length
closed MPO. This condition is not part of CPSV16 Definition 4.7.

Underlying source passage: arXiv:1606.00608, Definition 4.7, lines 815--822. -/
def IsNonvanishingSourceSimple (M : MPOTensor d D) : Prop :=
  IsSourceSimple M ∧ ∀ N : ℕ, 0 < N → mpo M N ≠ 0

/-- The strengthened nonvanishing predicate implies source simplicity. -/
theorem IsNonvanishingSourceSimple.isSourceSimple {M : MPOTensor d D}
    (hM : IsNonvanishingSourceSimple M) : IsSourceSimple M :=
  hM.1

/-- Source simplicity supplies a nonzero closed MPO at some positive length.

This is derived from the canonical-block convention preceding Definition 4.7.

Source: arXiv:1606.00608, lines 217--246 and Definition 4.7, lines 815--822. -/
theorem IsSourceSimple.exists_mpo_ne_zero {M : MPOTensor d D}
    (hM : IsSourceSimple M) : ∃ N : ℕ, 0 < N ∧ mpo M N ≠ 0 := by
  obtain ⟨_, L, hL, P, hPres, _⟩ := hM
  obtain ⟨N, hN, hStateNe⟩ := hPres.exists_pos_mpvState_ne_zero
  have hBlockedMpoNe : mpo (blockTensor M L) N ≠ 0 := by
    intro hZero
    apply hStateNe
    apply PiLp.ext
    intro ρ
    let σ : Fin N → Fin (MPSTensor.blockPhysDim d L) := fun n ↦ (ρ n).divNat
    let τ : Fin N → Fin (MPSTensor.blockPhysDim d L) := fun n ↦ (ρ n).modNat
    have hρ : (fun n ↦ finProdFinEquiv (σ n, τ n)) = ρ := by
      funext n
      exact finProdFinEquiv.apply_symm_apply (ρ n)
    rw [MPSTensor.mpvState_apply, ← hρ,
      MPSTensor.mpv_toMPSTensor_pairConfig, hZero]
    rfl
  refine ⟨N * L, Nat.mul_pos hN hL, ?_⟩
  intro hZero
  apply hBlockedMpoNe
  rw [mpo_blockTensor_eq_reindex, hZero]
  simp

/-- The strengthened predicate supplies nonvanishing at every positive length. -/
theorem IsNonvanishingSourceSimple.mpo_ne_zero {M : MPOTensor d D}
    (hM : IsNonvanishingSourceSimple M) (N : ℕ) (hN : 0 < N) : mpo M N ≠ 0 :=
  hM.2 N hN

/-- Normalized simplicity implies source simplicity.

The presentation is the normalized sector decomposition itself.  Its copy weights are
nonzero by construction, its representatives are normal and eventually linearly independent,
and the global gauge identifies its positive-length matrix-product vectors with those of the
blocked MPO tensor.  The nonnilpotency clause is unchanged because the representatives
themselves are unchanged.

Source: arXiv:1606.00608, Definition 4.7, lines 815--822, together with the
normalized sector decomposition at lines 238--246. -/
theorem IsSimple.isSourceSimple {M : MPOTensor d D} (hM : IsSimple M) :
    IsSourceSimple M := by
  classical
  obtain ⟨hMPDO, L, hL, -, S, hCF, hNonNil, hTotal, X, hEq⟩ := hM
  subst hTotal
  have hGauge : MPSTensor.GaugeEquiv S.toTensor (blockTensor M L).toMPSTensor :=
    ⟨MPSTensor.globalGaugeOfBlocks X, hEq⟩
  have : ∀ j, NeZero (S.basisDim j) := fun j ↦
    ⟨(hCF.basis_dim_pos j).ne'⟩
  refine ⟨hMPDO, L, hL, S, ?_, hNonNil⟩
  refine ⟨?_, ?_, ?_, hCF.bnt_data⟩
  · obtain ⟨j, _, _⟩ := hCF.weight_unit_exists
    exact Fin.pos_iff_nonempty.mpr ⟨j⟩
  · intro N _ σ
    exact (hGauge.sameMPV N σ).symm
  · intro j
    exact MPSTensor.isNormalTensor_of_isNormal_leftCanonical (S.basis j)
      (hCF.basis_isNormal j) (hCF.basis_left_canonical j)

/-- Normalized simplicity implies the strengthened nonvanishing source predicate
when every positive-length closed MPO is nonzero.

The nonvanishing assumption is additional to CPSV16 Definition 4.7. -/
theorem IsSimple.isNonvanishingSourceSimple {M : MPOTensor d D} (hM : IsSimple M)
    (hM_ne : ∀ N : ℕ, 0 < N → mpo M N ≠ 0) :
    IsNonvanishingSourceSimple M :=
  ⟨hM.isSourceSimple, hM_ne⟩

end MPOTensor

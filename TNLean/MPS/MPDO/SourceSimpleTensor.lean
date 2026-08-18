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
Definition 4.7. The generated family must be nontrivial at some positive length.
After a positive physical blocking, the doubled-index tensor must admit a CPSV
basis of normal tensors, and the ket-against-bra contraction of every basis
element must be nonnilpotent. The source definition does not require every
positive-length generated MPO to be nonzero and excludes the separate line-246
unit-weight normalization. The strengthened all-length nonvanishing interface is
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
  canonical-block convention at lines 217--246 and Definition 4.7 at lines
  815--822
-/

namespace MPOTensor

variable {d D : ℕ}

/-- **Normalization-free Definition 4.7 simplicity.** A tensor is source-simple
when it generates an MPDO, its closed MPO family is nontrivial at some positive
length, and, after some positive physical blocking, its doubled-index tensor has
a CPSV basis of normal tensors whose ket-against-bra contractions are all
nonnilpotent.

The existential nontriviality clause records the standing active-canonical-block
convention used before Definition 4.7; it excludes the identically zero closed-MPO
family even though the raw BNT predicate admits empty or dormant witnesses. It does
not eliminate dormant extra BNT candidates or require nonvanishing at every positive
length. The BNT witness uses `MPSTensor.IsCPSVBasisOfNormalTensors`, rather than an
arbitrary family of canonical blocks. The predicate excludes the separate line-246
unit-weight normalization and makes no claim that every positive blocking has such a witness.

Source: arXiv:1606.00608, canonical-block convention at lines 217--246 and
Definition 4.7, lines 815--822. -/
def IsSourceSimple (M : MPOTensor d D) : Prop :=
  IsMPDO M ∧ (∃ N : ℕ, 0 < N ∧ mpo M N ≠ 0) ∧
    ∃ L : ℕ, 0 < L ∧
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

/-- Source simplicity supplies a nonzero closed MPO at some positive length. -/
theorem IsSourceSimple.exists_mpo_ne_zero {M : MPOTensor d D}
    (hM : IsSourceSimple M) : ∃ N : ℕ, 0 < N ∧ mpo M N ≠ 0 :=
  hM.2.1

/-- The strengthened interface supplies nonvanishing at every positive length. -/
theorem IsNonvanishingSourceSimple.mpo_ne_zero {M : MPOTensor d D}
    (hM : IsNonvanishingSourceSimple M) (N : ℕ) (hN : 0 < N) : mpo M N ≠ 0 :=
  hM.2 N hN

/-- Normalized simplicity implies source simplicity.

The CPSV basis is the family of distinct normal representatives in the
normalized sector decomposition. Eventual linear independence and the fact that
a sector power sum is not eventually zero produce a nonzero blocked-chain state.
The global gauge preserves that state, and physical unblocking yields a nonzero
closed MPO at a positive multiple of the blocking length. The same gauge
transports the basis to the blocked MPO tensor. The nonnilpotency clause is
unchanged because the representatives themselves are unchanged.

Source: arXiv:1606.00608, Definition 4.7, lines 815--822, together with the
normalized fixed-representative interface of lines 238--246. -/
theorem IsSimple.isSourceSimple {M : MPOTensor d D} (hM : IsSimple M) :
    IsSourceSimple M := by
  classical
  obtain ⟨hMPDO, L, hL, -, S, hCF, hNonNil, hTotal, X, hEq⟩ := hM
  subst hTotal
  have hGauge : MPSTensor.GaugeEquiv S.toTensor (blockTensor M L).toMPSTensor :=
    ⟨MPSTensor.globalGaugeOfBlocks X, hEq⟩
  have hNontrivial : ∃ K : ℕ, 0 < K ∧ mpo M K ≠ 0 := by
    obtain ⟨N₀, hLI⟩ := hCF.bnt_data
    obtain ⟨j, -, -⟩ := hCF.weight_unit_exists
    have hCoeff : ∃ N : ℕ, N₀ < N ∧ S.coeff N j ≠ 0 := by
      by_contra h
      push Not at h
      apply hCF.coeff_not_eventually_zero j
      rw [Filter.eventually_atTop]
      exact ⟨N₀ + 1, fun N hN ↦ h N (by omega)⟩
    obtain ⟨N, hN, hCoeffN⟩ := hCoeff
    have hStateExpansion : MPSTensor.mpvState S.toTensor N =
        ∑ k : Fin S.basisCount,
          S.coeff N k • MPSTensor.mpvState (S.basis k) N := by
      refine MPSTensor.mpvState_eq_sum_of_decomp S.toTensor S.basis (S.coeff N) ?_
      intro σ
      simpa [smul_eq_mul] using S.mpv_toTensor_eq_sum_coeff σ
    have hStateNe : MPSTensor.mpvState S.toTensor N ≠ 0 := by
      rw [hStateExpansion]
      intro hzero
      exact hCoeffN ((Fintype.linearIndependent_iff.mp (hLI N hN)) _ hzero j)
    have hBlockedStateNe :
        MPSTensor.mpvState (blockTensor M L).toMPSTensor N ≠ 0 := by
      have hStateEq : MPSTensor.mpvState (blockTensor M L).toMPSTensor N =
          MPSTensor.mpvState S.toTensor N := by
        apply PiLp.ext
        intro ρ
        simpa only [MPSTensor.mpvState_apply] using (hGauge.sameMPV N ρ).symm
      rw [hStateEq]
      exact hStateNe
    have hBlockedMpoNe : mpo (blockTensor M L) N ≠ 0 := by
      intro hzero
      apply hBlockedStateNe
      apply PiLp.ext
      intro ρ
      let σ : Fin N → Fin (MPSTensor.blockPhysDim d L) := fun n ↦ (ρ n).divNat
      let τ : Fin N → Fin (MPSTensor.blockPhysDim d L) := fun n ↦ (ρ n).modNat
      have hρ : (fun n ↦ finProdFinEquiv (σ n, τ n)) = ρ := by
        funext n
        exact finProdFinEquiv.apply_symm_apply (ρ n)
      rw [MPSTensor.mpvState_apply, ← hρ,
        MPSTensor.mpv_toMPSTensor_pairConfig, hzero]
      rfl
    refine ⟨N * L, Nat.mul_pos (by omega) hL, ?_⟩
    intro hzero
    apply hBlockedMpoNe
    rw [mpo_blockTensor_eq_reindex, hzero]
    simp
  refine ⟨hMPDO, hNontrivial, L, hL, S.basisCount,
    fun j ↦ ⟨S.basisDim j, S.basis j⟩, ?_, hNonNil⟩
  have hBNT : MPSTensor.IsCPSVBasisOfNormalTensors S.toTensor
      (fun j ↦ ⟨S.basisDim j, S.basis j⟩) := by
    let : ∀ j : Fin S.basisCount, NeZero (S.basisDim j) :=
      fun j ↦ ⟨(hCF.basis_dim_pos j).ne'⟩
    refine {
      blocks_normal := fun j ↦
        MPSTensor.isNormalTensor_of_isNormal_leftCanonical (S.basis j)
          (hCF.basis_isNormal j) (hCF.basis_left_canonical j)
      spans_mpv := fun N _ ↦ ⟨S.coeff N, fun σ ↦ S.mpv_toTensor_eq_sum_coeff σ⟩
      eventually_li := hCF.bnt_data }
  apply hBNT.of_sameMPV₂Pos
  intro N _ σ
  exact hGauge.sameMPV N σ

/-- Normalized simplicity implies the strengthened nonvanishing source interface
when every positive-length closed MPO is nonzero.

The nonvanishing assumption is additional to CPSV16 Definition 4.7. -/
theorem IsSimple.isNonvanishingSourceSimple {M : MPOTensor d D} (hM : IsSimple M)
    (hM_ne : ∀ N : ℕ, 0 < N → mpo M N ≠ 0) :
    IsNonvanishingSourceSimple M :=
  ⟨hM.isSourceSimple, hM_ne⟩

end MPOTensor

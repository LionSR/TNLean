/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.BNTRefinement
import TNLean.MPS.CanonicalForm.CPSVPhysicalReindex
import TNLean.MPS.MPDO.SimpleTensor

/-!
# Definition 4.7 simplicity

This module records simplicity in the sense of arXiv:1606.00608,
Definition 4.7. After a positive physical blocking, the doubled-index tensor
must have a sector presentation by a basis of normal tensors, and the
ket-against-bra contraction of every representative must be nonnilpotent. The
definition does not require every positive-length generated MPO to be nonzero
and excludes the separate line-246 unit-weight normalization. The presentation
implies positive-length nontriviality, which is therefore a theorem rather than
a defining clause.

## Main results

* `MPOTensor.IsSimple`: Definition 4.7 read over the canonical blocks.
* `MPOTensor.IsSimpleCanonicalForm.isSimple`: the fixed-representative canonical
  package implies source-facing simplicity.
* `MPOTensor.IsSimple.exists_mpo_ne_zero`: simplicity supplies a nonzero closed
  MPO at some positive chain length.

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

/-- **Definition 4.7 simplicity.** A tensor is simple when it generates an MPDO and,
after some positive physical blocking, its doubled-index tensor has a sector
presentation by a basis of normal tensors whose ket-against-bra contractions are all
nonnilpotent.

Every representative has a positive number of copies, every copy has nonzero weight, and
distinct representatives are eventually linearly independent.  Thus positive-length
nontriviality follows rather than being postulated.  The predicate excludes the separate
line-246 unit-weight normalization and makes no claim that every positive blocking has such
a witness.

Source: arXiv:1606.00608, canonical-block convention at lines 217--246 and
Definition 4.7, lines 815--822. -/
def IsSimple (M : MPOTensor d D) : Prop :=
  IsMPDO M ∧
    ∃ L : ℕ, 0 < L ∧
      ∃ P : MPSTensor.SectorDecomposition
          (MPSTensor.blockPhysDim d L * MPSTensor.blockPhysDim d L),
        MPSTensor.IsBNTSectorPresentation
            (blockTensor M L).toMPSTensor P ∧
          ∀ j, ¬ IsNilpotent
            (doubledPhysTraceTransfer (MPSTensor.blockPhysDim d L) (P.basis j))

/-- A simple canonical-form tensor is simple in the source-facing sense of
Definition 4.7.

Take blocking length $L=1$ and relabel the displayed BNT by the canonical
identification between the one-site blocked ket-bra alphabet and the original
doubled alphabet. The global block gauge preserves every closed
matrix-product coefficient, while this relabeling preserves normality and the
physical-trace transfer of each representative. Hence the displayed
nonnilpotency certificates give the required BNT presentation after blocking.

The implication forgets the line-246 unit-weight normalization built into
`IsSimpleCanonicalForm`; that normalization is not part of `IsSimple`.

Source: arXiv:1606.00608, canonical form at lines 217--246 and Definition 4.7
at lines 815--822. -/
theorem IsSimpleCanonicalForm.isSimple {M : MPOTensor d D}
    (hM : IsSimpleCanonicalForm M) : IsSimple M := by
  obtain ⟨hMPDO, S, hCF, hNonNil, hTotal, X, hEq⟩ := hM
  subst D
  let e : Fin (MPSTensor.blockPhysDim d 1 * MPSTensor.blockPhysDim d 1) ≃ Fin (d * d) :=
    finProdFinEquiv.symm |>.trans
      (Equiv.prodCongr (MPSTensor.singleBlockEquiv d) (MPSTensor.singleBlockEquiv d)) |>.trans
        finProdFinEquiv
  let P : MPSTensor.SectorDecomposition
      (MPSTensor.blockPhysDim d 1 * MPSTensor.blockPhysDim d 1) := {
    basisCount := S.basisCount
    basisDim := S.basisDim
    basis := fun j ↦ Kraus.reindexPhysical e (S.basis j)
    sectors := S.sectors }
  have hGauge : MPSTensor.GaugeEquiv S.toTensor M.toMPSTensor := by
    refine ⟨MPSTensor.globalGaugeOfBlocks X, ?_⟩
    intro i
    simpa using hEq i
  have hSame : MPSTensor.SameMPV₂Pos M.toMPSTensor S.toTensor :=
    MPSTensor.SameMPV₂.toSameMPV₂Pos (fun N σ => (hGauge.sameMPV N σ).symm)
  have hBlock : (blockTensor M 1).toMPSTensor =
      Kraus.reindexPhysical e M.toMPSTensor := by
    funext ij
    change
      M (MPSTensor.singleBlockEquiv d ij.divNat)
          (MPSTensor.singleBlockEquiv d ij.modNat) * 1 =
        M (e ij).divNat (e ij).modNat
    simp [e]
  refine ⟨hMPDO, 1, Nat.one_pos, P, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · obtain ⟨j, _q, _hj⟩ := hCF.weight_unit_exists
      exact Fin.pos_iff_nonempty.mpr ⟨j⟩
    · intro N hN σ
      rw [hBlock]
      change MPSTensor.mpv (Kraus.reindexPhysical e M.toMPSTensor) σ =
        MPSTensor.mpv (Kraus.reindexPhysical e S.toTensor) σ
      simp only [MPSTensor.mpv_reindexPhysical]
      exact hSame N hN (fun n => e (σ n))
    · let _ : ∀ j : Fin S.basisCount, NeZero (S.basisDim j) :=
        fun j => ⟨(hCF.basis_dim_pos j).ne'⟩
      intro j
      exact (MPSTensor.isNormalTensor_of_isNormal_leftCanonical (S.basis j)
        (hCF.basis_isNormal j) (hCF.basis_left_canonical j)).reindexPhysical e
    · obtain ⟨N₀, hLI⟩ := hCF.bnt_data
      refine ⟨N₀, fun N hN ↦ ?_⟩
      exact MPSTensor.linearIndependent_mpvState_reindexPhysical_equiv e S.basis (hLI N hN)
  · intro j
    change ¬ IsNilpotent (doubledPhysTraceTransfer (MPSTensor.blockPhysDim d 1)
      (Kraus.reindexPhysical e (S.basis j)))
    have hTransfer :
        doubledPhysTraceTransfer (MPSTensor.blockPhysDim d 1)
            (Kraus.reindexPhysical e (S.basis j)) =
          doubledPhysTraceTransfer d (S.basis j) := by
      rw [doubledPhysTraceTransfer, doubledPhysTraceTransfer]
      change (∑ i : Fin (MPSTensor.blockPhysDim d 1),
          S.basis j (e (finProdFinEquiv (i, i)))) =
        ∑ i : Fin d, S.basis j (finProdFinEquiv (i, i))
      simpa [e] using (MPSTensor.singleBlockEquiv d).sum_comp
        (fun i : Fin d => S.basis j (finProdFinEquiv (i, i)))
    rw [hTransfer]
    exact hNonNil j

/-- Simplicity supplies a nonzero closed MPO at some positive length.

This is derived from the canonical-block convention preceding Definition 4.7.

Source: arXiv:1606.00608, lines 217--246 and Definition 4.7, lines 815--822. -/
theorem IsSimple.exists_mpo_ne_zero {M : MPOTensor d D}
    (hM : IsSimple M) : ∃ N : ℕ, 0 < N ∧ mpo M N ≠ 0 := by
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

end MPOTensor

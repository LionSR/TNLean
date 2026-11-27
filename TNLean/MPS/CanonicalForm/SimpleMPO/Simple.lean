/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.BNTPresentation.Refinement
import TNLean.MPS.CanonicalForm.BNTPresentation.SectorBlocking
import TNLean.MPS.CanonicalForm.SimpleMPO.SimpleTensor
import TNLean.MPS.CanonicalForm.PhysicalReindex

/-!
# Definition 4.7 simplicity

This module records simplicity in the sense of arXiv:1606.00608,
Definition 4.7. After a positive physical blocking, the tensor on the pair alphabet
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

namespace MPSTensor

open MPTensor

/-- A bijective relabelling of the physical alphabet transports a basis-of-normal-tensors
presentation.

Source: arXiv:1606.00608, the physical-basis identifications used at lines 317--345. -/
theorem IsBNTSectorPresentation.reindexPhysical {α α' : Type*} [Fintype α] [Fintype α']
    {D' : ℕ} {A : MPTensor α (Fin D')} {P : SectorDecomposition α}
    (h : IsBNTSectorPresentation A P) (e : α' ≃ α) :
    IsBNTSectorPresentation (Kraus.reindexPhysical e A) (P.reindexPhysical e) where
  basisCount_pos := h.basisCount_pos
  sameMPV₂Pos N hN σ := by
    rw [SectorDecomposition.reindexPhysical_toTensor, MPTensor.mpv_reindexPhysical,
      MPTensor.mpv_reindexPhysical]
    exact h.sameMPV₂Pos N hN _
  basis_normal j := (h.basis_normal j).reindexPhysical e
  eventually_li := by
    obtain ⟨N₀, hLI⟩ := h.eventually_li
    exact ⟨N₀, fun N hN ↦ linearIndependent_mpvState_reindexPhysical_equiv e P.basis (hLI N hN)⟩

end MPSTensor

namespace MPSTensor.IsBNTCanonicalForm

/-- Every representative of a BNT canonical form is a normal tensor.

The physical alphabet is relabelled by `Fin (Fintype.card α)`, on which irreducibility,
left-canonicality and normalized self-overlap give normality.

Source: arXiv:1606.00608, lines 224--235 and 271--274; the period-one characterization is the
non-periodic canonical-form condition of arXiv:2011.12127, lines 1815--1837. -/
theorem basis_isNormalTensor {α : Type*} [Fintype α] {S : SectorDecomposition α}
    (hCF : IsBNTCanonicalForm S) (j : Fin S.basisCount) :
    MPTensor.IsNormalTensor (S.basis j) := by
  classical
  let f : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
  have hCF' := SectorDecomposition.IsBNTCanonicalForm.reindexPhysical hCF f
  let _ : NeZero ((S.reindexPhysical f).basisDim j) := ⟨(hCF'.basis_dim_pos j).ne'⟩
  have h := (isNormalTensor_of_isNormal_leftCanonical ((S.reindexPhysical f).basis j)
    (hCF'.basis_isNormal j) (hCF'.basis_left_canonical j)).reindexPhysical f.symm
  have hback : Kraus.reindexPhysical f.symm ((S.reindexPhysical f).basis j) = S.basis j := by
    funext i
    simp [Kraus.reindexPhysical]
  rwa [hback] at h

end MPSTensor.IsBNTCanonicalForm

namespace MPOTensor

variable {d D : ℕ}

/-- Two BNT presentations of tensors with the same positive-length matrix product vectors have
gauge-phase equivalent representatives, matched by a bijection.

The physical alphabet is relabelled by `Fin (Fintype.card α)`, where the uniqueness theorem
`IsBNTSectorPresentation.equiv_of_sameMPV₂Pos` applies.

Source: arXiv:1606.00608, Proposition 2.7, lines 1135--1148. -/
private theorem exists_basis_gaugePhaseEquiv_of_presentations {α : Type*} [Fintype α]
    {D₁ : ℕ} {A : MPTensor α (Fin D₁)} {P Q : MPSTensor.SectorDecomposition α}
    (hP : MPSTensor.IsBNTSectorPresentation A P)
    (hQ : MPSTensor.IsBNTSectorPresentation A Q) :
    ∃ e : Fin P.basisCount ≃ Fin Q.basisCount, ∀ j : Fin P.basisCount,
      ∃ hdim : P.basisDim j = Q.basisDim (e j),
        MPTensor.GaugePhaseEquiv
          (cast (congr_arg (fun n ↦ MPTensor α (Fin n)) hdim) (P.basis j)) (Q.basis (e j)) := by
  classical
  let f : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
  obtain ⟨e, hEquiv⟩ := (hP.reindexPhysical f).equiv_of_sameMPV₂Pos (hQ.reindexPhysical f)
    (fun _ _ _ ↦ rfl)
  refine ⟨e, fun j ↦ ?_⟩
  obtain ⟨hdim, hGauge⟩ := hEquiv j
  refine ⟨hdim, ?_⟩
  have hG := hGauge.toGaugePhaseEquiv
  change MPTensor.GaugePhaseEquiv
    (cast (congr_arg (fun n ↦ MPTensor (Fin (Fintype.card α)) (Fin n)) hdim)
      (Kraus.reindexPhysical f (P.basis j))) (Kraus.reindexPhysical f (Q.basis (e j))) at hG
  rw [← MPSTensor.reindexPhysical_cast_dim f hdim (P.basis j)] at hG
  exact (MPSTensor.gaugePhaseEquiv_reindexPhysical_equiv f _ _).1 hG

/-- Nonnilpotency of all BNT representatives is independent of the chosen presentation.

The BNT uniqueness theorem matches representatives by permutation, equal bond
dimension, gauge, and phase.  Similarity, nonzero scalar multiplication, and the resulting
dimension identification preserve nilpotency of the physical-trace transfer.

Source: arXiv:1606.00608, Definition 4.7, lines 815--822, and Proposition 2.7,
lines 1135--1148. -/
theorem bnt_basis_not_isNilpotent_iff
    {D' p : ℕ} {A : MPOTensor p D'}
    {P Q : MPSTensor.SectorDecomposition (Fin p × Fin p)}
    (hP : MPSTensor.IsBNTSectorPresentation A P)
    (hQ : MPSTensor.IsBNTSectorPresentation A Q) :
    (∀ j, ¬ IsNilpotent (physTraceTransfer (P.basis j))) ↔
      ∀ k, ¬ IsNilpotent (physTraceTransfer (Q.basis k)) := by
  classical
  obtain ⟨e, hEquiv⟩ := exists_basis_gaugePhaseEquiv_of_presentations hP hQ
  constructor
  · intro hPNonNil k hQNil
    let j := e.symm k
    obtain ⟨hdim, hGauge⟩ := hEquiv j
    have hQNil' : IsNilpotent (physTraceTransfer (Q.basis (e j))) := by
      rw [e.apply_symm_apply]
      exact hQNil
    have hCastNil : IsNilpotent
        (physTraceTransfer
          (cast (congr_arg (fun n ↦ MPTensor (Fin p × Fin p) (Fin n)) hdim) (P.basis j))) :=
      (isNilpotent_physTraceTransfer_iff_of_gaugePhaseEquiv hGauge).mpr hQNil'
    exact hPNonNil j
      ((isNilpotent_physTraceTransfer_cast_iff hdim (P.basis j)).mp hCastNil)
  · intro hQNonNil j hPNil
    obtain ⟨hdim, hGauge⟩ := hEquiv j
    have hCastNil : IsNilpotent
        (physTraceTransfer
          (cast (congr_arg (fun n ↦ MPTensor (Fin p × Fin p) (Fin n)) hdim) (P.basis j))) :=
      (isNilpotent_physTraceTransfer_cast_iff hdim (P.basis j)).mpr hPNil
    exact hQNonNil (e j)
      ((isNilpotent_physTraceTransfer_iff_of_gaugePhaseEquiv hGauge).mp hCastNil)

/-- **Definition 4.7 simplicity.** A tensor is simple when it generates an MPDO and,
after some positive physical blocking, its tensor on the pair alphabet has a sector
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
          (Fin (Kraus.blockPhysDim d L) × Fin (Kraus.blockPhysDim d L)),
        MPSTensor.IsBNTSectorPresentation (blockTensor M L) P ∧
          ∀ j, ¬ IsNilpotent (physTraceTransfer (P.basis j))

/-- A simple canonical-form tensor is simple in the source-facing sense of
Definition 4.7.

Take blocking length $L=1$ and relabel the displayed BNT by the canonical
identification between the one-site blocked ket-bra alphabet and the original
pair alphabet. The global block gauge preserves every closed
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
  let e : Fin (Kraus.blockPhysDim d 1) × Fin (Kraus.blockPhysDim d 1) ≃ Fin d × Fin d :=
    Equiv.prodCongr (Kraus.singleBlockEquiv d) (Kraus.singleBlockEquiv d)
  let P := S.reindexPhysical e
  have hGauge : MPTensor.GaugeEquiv S.toTensor M := by
    refine ⟨MPSTensor.globalGaugeOfBlocks X, ?_⟩
    intro i
    simpa using hEq i
  have hSame : MPTensor.SameMPV₂Pos M S.toTensor :=
    MPTensor.SameMPV₂.toSameMPV₂Pos (fun N σ => (hGauge.sameMPV N σ).symm)
  have hBlock : blockTensor M 1 = Kraus.reindexPhysical e M := by
    funext ⟨a, b⟩
    change M (Kraus.singleBlockEquiv d a, Kraus.singleBlockEquiv d b) * 1 =
      M (Kraus.singleBlockEquiv d a, Kraus.singleBlockEquiv d b)
    rw [Matrix.mul_one]
  refine ⟨hMPDO, 1, Nat.one_pos, P, ?_, ?_⟩
  · have hCF' :=
      MPSTensor.SectorDecomposition.IsBNTCanonicalForm.reindexPhysical hCF e
    refine ⟨?_, ?_, ?_, hCF'.bnt_data⟩
    · obtain ⟨j, _q, _hj⟩ := hCF.weight_unit_exists
      exact Fin.pos_iff_nonempty.mpr ⟨j⟩
    · intro N hN σ
      rw [hBlock]
      change MPTensor.mpv (Kraus.reindexPhysical e M) σ =
        MPTensor.mpv (Kraus.reindexPhysical e S.toTensor) σ
      simp only [MPTensor.mpv_reindexPhysical]
      exact hSame N hN (fun n => e (σ n))
    · intro j
      exact hCF'.basis_isNormalTensor j
  · intro j
    change ¬ IsNilpotent (physTraceTransfer (Kraus.reindexPhysical e (S.basis j)))
    have hTransfer :
        physTraceTransfer (Kraus.reindexPhysical e (S.basis j)) =
          physTraceTransfer (S.basis j) := by
      simp only [physTraceTransfer, Kraus.reindexPhysical]
      exact (Kraus.singleBlockEquiv d).sum_comp (fun i : Fin d => S.basis j (i, i))
    rw [hTransfer]
    exact hNonNil j

/-- Simplicity supplies a nonzero closed MPO at some positive length.

This is derived from the canonical-block convention preceding Definition 4.7.

Source: arXiv:1606.00608, lines 217--246 and Definition 4.7, lines 815--822. -/
theorem IsSimple.exists_mpo_ne_zero {M : MPOTensor d D}
    (hM : IsSimple M) : ∃ N : ℕ, 0 < N ∧ mpo M N ≠ 0 := by
  classical
  obtain ⟨_, L, hL, P, hPres, _⟩ := hM
  let f := (Fintype.equivFin (Fin (Kraus.blockPhysDim d L) × Fin (Kraus.blockPhysDim d L))).symm
  obtain ⟨N, hN, hStateNe⟩ := (hPres.reindexPhysical f).exists_pos_mpvState_ne_zero
  have hBlockedMpoNe : mpo (blockTensor M L) N ≠ 0 := by
    intro hZero
    apply hStateNe
    apply PiLp.ext
    intro ρ
    rw [MPSTensor.mpvState_apply, MPTensor.mpv_reindexPhysical, mpv_eq_mpo, hZero]
    rfl
  refine ⟨N * L, Nat.mul_pos hN hL, ?_⟩
  intro hZero
  apply hBlockedMpoNe
  rw [mpo_blockTensor_eq_reindex, hZero]
  simp

end MPOTensor

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.Assembly.StructuralData
import TNLean.MPS.CanonicalForm.Assembly.CommonBlockedCyclicSectorRepresentatives

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Filter

namespace MPSTensor

/-!
# Common-sector transport after canonical-form blocking

This module contains the zero-tail transport lemmas and common-sector
reindexing hypotheses used after the structural canonical-form reduction has
produced common cyclic-sector data.

Here "zero-tail" means the total bond dimension of the separated all-zero
leftover blocks in the block decomposition.  It is the dimension gap allowed by
`∑ k, D_k ≤ D`, where the remaining summands are zero blocks.

## Main statements

* `zeroTail_commonFlat_of_reindexed` and
  `sameMPV₂Pos_blockTensor_commonFlatAt_of_reindexed` transport zero-tail
  decompositions through the common-sector relabeling data.
* `CommonSectorRelabelingHypothesis` and
  `CommonGroupedBlockCastHypothesis` package the remaining blocked-word
  comparison data.
* `afterBlocking_commonPrimitiveIrreducibleBlocks_of_reindexedNonzeroParts`
  and `unconditional_commonPrimitiveIrreducibleBlocks` turn the structural
  common-sector data into common primitive irreducible block decompositions.

## References

* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608, Section 2.3 + Appendix A]
* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:2011.12127, Section IV]

## Tags

matrix product states, canonical form, common sectors, zero-tail decomposition
-/

/-- The representative common-sector family is normal-CF-BNT once the
representative weights are strictly ordered and the representatives are
BNT-separated.

It combines the representative normal-canonical-form statement with the
explicit hypothesis that distinct representatives are not gauge-phase equivalent. -/
theorem isNormalCanonicalFormBNT_commonRepresentativeBlocksAt
    {d r : ℕ} {dim : Fin r → ℕ}
    {blocks : (k : Fin r) → MPSTensor d (dim k)}
    (F : CommonBlockedCyclicSectorFamily blocks)
    {p : ℕ} (hp : F.p = p)
    (μ : Fin r → ℂ)
    (hμ : ∀ k, μ k ≠ 0)
    (hAnti : StrictAnti (fun k : Fin r => ‖F.commonRepresentativeWeight μ k‖))
    (hNotGpe : BlocksNotGaugePhaseEquiv
      (d := blockPhysDim d p) (F.commonRepresentativeBlocksAt hp)) :
    IsNormalCanonicalFormBNT (d := blockPhysDim d p)
      (F.commonRepresentativeWeight μ) (F.commonRepresentativeBlocksAt hp) where
  toIsNormalCanonicalForm :=
    F.isNormalCanonicalForm_commonRepresentativeBlocksAt hp μ hμ hAnti.antitone
  mu_strict_anti := hAnti
  blocks_not_equiv := hNotGpe

/-- If each directly blocked nonzero block agrees with its iterated-blocking version,
the zero-tail equation can be written using the derived common-sector family. -/
lemma zeroTail_commonFlat_of_blockwise
    {d D r z : ℕ} {dim : Fin r → ℕ}
    (A : MPSTensor d D) (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (F : CommonBlockedCyclicSectorFamily blocks)
    (hMPV : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv A σ = mpv (zeroMPSTensor d z) σ +
        mpv (toTensorFromBlocks (d := d) (μ := μ) blocks) σ)
    (hBlock : ∀ k : Fin r,
      SameMPV₂
        (blockTensor (d := d) (D := dim k) (blocks k) F.p)
        (F.commonReindexedBlock k)) :
    ∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d F.p)),
      mpv (blockTensor (d := d) (D := D) A F.p) σ =
        mpv (zeroMPSTensor (blockPhysDim d F.p) z) σ +
          mpv (toTensorFromBlocks (d := blockPhysDim d F.p)
            (μ := F.commonFlatWeight μ) F.commonFlatBlocks) σ := by
  have hCanon := zeroTail_toTensorFromBlocks_blockPower
    (d := d) (D := D) (r := r) (z := z) (p := F.p) (dim := dim)
    A μ blocks F.p_pos hMPV
  have hFlat := F.sameMPV₂_weightedCanonicalBlock_commonFlat_of_blockwise μ hBlock
  exact zeroTail_eq_of_sameMPV₂ _ _ _ hCanon hFlat

/-- If the blocked-word decodings agree for every nonzero block, the zero-tail equation
can be written using the derived common-sector family. -/
lemma zeroTail_commonFlat_of_word_eq
    {d D r z : ℕ} {dim : Fin r → ℕ}
    (A : MPSTensor d D) (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (F : CommonBlockedCyclicSectorFamily blocks)
    (hMPV : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv A σ = mpv (zeroMPSTensor d z) σ +
        mpv (toTensorFromBlocks (d := d) (μ := μ) blocks) σ)
    (hWord : ∀ (k : Fin r) (i : Fin (blockPhysDim d F.p)),
      wordOfBlock d F.p i =
        wordOfBlock d (F.period k * F.extra k)
          (iteratedBlockIndex d (F.period k) (F.extra k)
            (Fin.cast ((F.blockPhysDim_nested_eq k).symm) i))) :
    ∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d F.p)),
      mpv (blockTensor (d := d) (D := D) A F.p) σ =
        mpv (zeroMPSTensor (blockPhysDim d F.p) z) σ +
          mpv (toTensorFromBlocks (d := blockPhysDim d F.p)
            (μ := F.commonFlatWeight μ) F.commonFlatBlocks) σ := by
  exact zeroTail_commonFlat_of_blockwise A μ blocks F hMPV
    (fun k => F.blockTensor_sameMPV₂_commonReindexedBlock_of_word_eq k (hWord k))

/-- If the canonical identifications agree with consecutive grouping for every nonzero block,
the zero-tail equation can be written using the derived common-sector family. -/
lemma zeroTail_commonFlat_of_groupedBlockCastAgrees
    {d D r z : ℕ} {dim : Fin r → ℕ}
    (A : MPSTensor d D) (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (F : CommonBlockedCyclicSectorFamily blocks)
    (hMPV : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv A σ = mpv (zeroMPSTensor d z) σ +
        mpv (toTensorFromBlocks (d := d) (μ := μ) blocks) σ)
    (hCast : ∀ k : Fin r, F.groupedBlockCastAgrees k) :
    ∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d F.p)),
      mpv (blockTensor (d := d) (D := D) A F.p) σ =
        mpv (zeroMPSTensor (blockPhysDim d F.p) z) σ +
          mpv (toTensorFromBlocks (d := blockPhysDim d F.p)
            (μ := F.commonFlatWeight μ) F.commonFlatBlocks) σ := by
  exact zeroTail_commonFlat_of_blockwise A μ blocks F hMPV
    (fun k => F.blockTensor_sameMPV₂_commonReindexedBlock_of_groupedBlockCastAgrees k (hCast k))

/-- The preceding zero-tail rewriting from the coordinate-grouping condition, expressed at a
prescribed common length. -/
lemma zeroTail_commonFlatAt_of_groupedBlockCastAgrees
    {d D r z : ℕ} {dim : Fin r → ℕ}
    (A : MPSTensor d D) (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (F : CommonBlockedCyclicSectorFamily blocks)
    {p : ℕ} (hp : F.p = p)
    (hMPV : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv A σ = mpv (zeroMPSTensor d z) σ +
        mpv (toTensorFromBlocks (d := d) (μ := μ) blocks) σ)
    (hCast : ∀ k : Fin r, F.groupedBlockCastAgrees k) :
    ∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d p)),
      mpv (blockTensor (d := d) (D := D) A p) σ =
        mpv (zeroMPSTensor (blockPhysDim d p) z) σ +
          mpv (toTensorFromBlocks (d := blockPhysDim d p)
            (μ := F.commonFlatWeight μ) (F.commonFlatBlocksAt hp)) σ := by
  subst p
  simpa [CommonBlockedCyclicSectorFamily.commonFlatBlocksAt] using
    zeroTail_commonFlat_of_groupedBlockCastAgrees A μ blocks F hMPV hCast

/-- At positive lengths, the blocked tensor has the same MPV coefficients as the
weighted common-sector family whenever the coordinate-grouping condition holds. -/
lemma sameMPV₂Pos_blockTensor_commonFlatAt_of_groupedBlockCastAgrees
    {d D r z : ℕ} {dim : Fin r → ℕ}
    (A : MPSTensor d D) (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (F : CommonBlockedCyclicSectorFamily blocks)
    {p : ℕ} (hp : F.p = p)
    (hMPV : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv A σ = mpv (zeroMPSTensor d z) σ +
        mpv (toTensorFromBlocks (d := d) (μ := μ) blocks) σ)
    (hCast : ∀ k : Fin r, F.groupedBlockCastAgrees k) :
    SameMPV₂Pos
      (blockTensor (d := d) (D := D) A p)
      (toTensorFromBlocks (d := blockPhysDim d p)
        (μ := F.commonFlatWeight μ) (F.commonFlatBlocksAt hp)) := by
  have hZeroTail := zeroTail_commonFlatAt_of_groupedBlockCastAgrees
    (d := d) (D := D) (r := r) (z := z) (dim := dim)
    A μ blocks F hp hMPV hCast
  exact sameMPV₂Pos_of_zeroTail_eq _ _ hZeroTail

/-- If the canonical blocked nonzero part agrees with the common reindexed blocks,
the zero-tail equation can be rewritten using the derived common-sector family.
Thus the blocked tensor has the same MPV coefficients as the weighted common-sector
tensor, with the same all-zero-block contribution at length zero. -/
lemma zeroTail_commonFlat_of_reindexed
    {d D r z : ℕ} {dim : Fin r → ℕ}
    (A : MPSTensor d D) (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (F : CommonBlockedCyclicSectorFamily blocks)
    (hMPV : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv A σ = mpv (zeroMPSTensor d z) σ +
        mpv (toTensorFromBlocks (d := d) (μ := μ) blocks) σ)
    (hLabel : SameMPV₂
      (toTensorFromBlocks (d := blockPhysDim d F.p)
        (μ := fun k : Fin r => (μ k) ^ F.p)
        (fun k => blockTensor (d := d) (D := dim k) (blocks k) F.p))
      (toTensorFromBlocks (d := blockPhysDim d F.p)
        (μ := fun k : Fin r => (μ k) ^ F.p) F.commonReindexedBlock)) :
    ∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d F.p)),
      mpv (blockTensor (d := d) (D := D) A F.p) σ =
        mpv (zeroMPSTensor (blockPhysDim d F.p) z) σ +
          mpv (toTensorFromBlocks (d := blockPhysDim d F.p)
            (μ := F.commonFlatWeight μ) F.commonFlatBlocks) σ := by
  have hCanon := zeroTail_toTensorFromBlocks_blockPower
    (d := d) (D := D) (r := r) (z := z) (p := F.p) (dim := dim)
    A μ blocks F.p_pos hMPV
  have hFlat := F.sameMPV₂_weightedCanonicalBlock_commonFlat_of_reindexed μ hLabel
  exact zeroTail_eq_of_sameMPV₂ _ _ _ hCanon hFlat

/-- The preceding zero-tail rewriting expressed at a prescribed common length. -/
lemma zeroTail_commonFlatAt_of_reindexed
    {d D r z : ℕ} {dim : Fin r → ℕ}
    (A : MPSTensor d D) (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (F : CommonBlockedCyclicSectorFamily blocks)
    {p : ℕ} (hp : F.p = p)
    (hMPV : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv A σ = mpv (zeroMPSTensor d z) σ +
        mpv (toTensorFromBlocks (d := d) (μ := μ) blocks) σ)
    (hRelabel : SameMPV₂
      (toTensorFromBlocks (d := blockPhysDim d F.p)
        (μ := fun k : Fin r => (μ k) ^ F.p)
        (fun k => blockTensor (d := d) (D := dim k) (blocks k) F.p))
      (toTensorFromBlocks (d := blockPhysDim d F.p)
        (μ := fun k : Fin r => (μ k) ^ F.p) F.commonReindexedBlock)) :
    ∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d p)),
      mpv (blockTensor (d := d) (D := D) A p) σ =
        mpv (zeroMPSTensor (blockPhysDim d p) z) σ +
          mpv (toTensorFromBlocks (d := blockPhysDim d p)
            (μ := F.commonFlatWeight μ) (F.commonFlatBlocksAt hp)) σ := by
  subst p
  simpa [CommonBlockedCyclicSectorFamily.commonFlatBlocksAt] using
    zeroTail_commonFlat_of_reindexed A μ blocks F hMPV hRelabel

/-- At positive lengths, the blocked tensor has the same MPV coefficients as the
weighted common-sector family once the blocked words have been reindexed. -/
lemma sameMPV₂Pos_blockTensor_commonFlatAt_of_reindexed
    {d D r z : ℕ} {dim : Fin r → ℕ}
    (A : MPSTensor d D) (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (F : CommonBlockedCyclicSectorFamily blocks)
    {p : ℕ} (hp : F.p = p)
    (hMPV : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv A σ = mpv (zeroMPSTensor d z) σ +
        mpv (toTensorFromBlocks (d := d) (μ := μ) blocks) σ)
    (hRelabel : SameMPV₂
      (toTensorFromBlocks (d := blockPhysDim d F.p)
        (μ := fun k : Fin r => (μ k) ^ F.p)
        (fun k => blockTensor (d := d) (D := dim k) (blocks k) F.p))
      (toTensorFromBlocks (d := blockPhysDim d F.p)
        (μ := fun k : Fin r => (μ k) ^ F.p) F.commonReindexedBlock)) :
    SameMPV₂Pos
      (blockTensor (d := d) (D := D) A p)
      (toTensorFromBlocks (d := blockPhysDim d p)
        (μ := F.commonFlatWeight μ) (F.commonFlatBlocksAt hp)) := by
  have hZeroTail := zeroTail_commonFlatAt_of_reindexed
    (d := d) (D := D) (r := r) (z := z) (dim := dim)
    A μ blocks F hp hMPV hRelabel
  exact sameMPV₂Pos_of_zeroTail_eq _ _ hZeroTail

/-- Replacing nonzero parts by MPV-equivalent tensors preserves the positive-length
MPV equality and the length-zero zero-tail identity. -/
lemma sameMPV₂Pos_and_zeroTail_identity_of_sameMPV₂
    {d LA LB LA' LB' zeroTailA zeroTailB : ℕ}
    (liveA : MPSTensor d LA) (liveB : MPSTensor d LB)
    (flatA : MPSTensor d LA') (flatB : MPSTensor d LB')
    (hA : SameMPV₂ liveA flatA) (hB : SameMPV₂ liveB flatB)
    (hPos : SameMPV₂Pos liveA liveB)
    (hZero : ∀ σ : Fin 0 → Fin d,
      (zeroTailA : ℂ) + mpv liveA σ = (zeroTailB : ℂ) + mpv liveB σ) :
    SameMPV₂Pos flatA flatB ∧
      ∀ σ : Fin 0 → Fin d,
        (zeroTailA : ℂ) + mpv flatA σ = (zeroTailB : ℂ) + mpv flatB σ := by
  refine ⟨?_, ?_⟩
  · intro N hN σ
    calc
      mpv flatA σ = mpv liveA σ := (hA N σ).symm
      _ = mpv liveB σ := hPos N hN σ
      _ = mpv flatB σ := hB N σ
  · intro σ
    calc
      (zeroTailA : ℂ) + mpv flatA σ = (zeroTailA : ℂ) + mpv liveA σ := by
        rw [(hA 0 σ).symm]
      _ = (zeroTailB : ℂ) + mpv liveB σ := hZero σ
      _ = (zeroTailB : ℂ) + mpv flatB σ := by
        rw [hB 0 σ]

/-- Once the canonical blocked nonzero part agrees with the reindexed common-sector
nonzero part, the zero-tail equation, the transported-weight equality, and the
nonvanishing of the common-sector weights are available together. -/
lemma zeroTail_commonFlat_transport_of_reindexed
    {d D r z : ℕ} {dim : Fin r → ℕ}
    (A : MPSTensor d D) (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (F : CommonBlockedCyclicSectorFamily blocks)
    (hμ : ∀ k, μ k ≠ 0)
    (hMPV : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv A σ = mpv (zeroMPSTensor d z) σ +
        mpv (toTensorFromBlocks (d := d) (μ := μ) blocks) σ)
    (hRelabel : SameMPV₂
      (toTensorFromBlocks (d := blockPhysDim d F.p)
        (μ := fun k : Fin r => (μ k) ^ F.p)
        (fun k => blockTensor (d := d) (D := dim k) (blocks k) F.p))
      (toTensorFromBlocks (d := blockPhysDim d F.p)
        (μ := fun k : Fin r => (μ k) ^ F.p) F.commonReindexedBlock)) :
    (∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d F.p)),
      mpv (blockTensor (d := d) (D := D) A F.p) σ =
        mpv (zeroMPSTensor (blockPhysDim d F.p) z) σ +
          mpv (toTensorFromBlocks (d := blockPhysDim d F.p)
            (μ := F.commonFlatWeight μ) F.commonFlatBlocks) σ) ∧
    SameMPV₂
      (toTensorFromBlocks (d := blockPhysDim d F.p)
        (μ := fun k : Fin r => (μ k) ^ F.p)
        (fun k => blockTensor (d := d) (D := dim k) (blocks k) F.p))
      (toTensorFromBlocks (d := blockPhysDim d F.p)
        (μ := F.commonFlatWeight μ) F.commonFlatBlocks) ∧
    (∀ x, F.commonFlatWeight μ x ≠ 0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact zeroTail_commonFlat_of_reindexed A μ blocks F hMPV hRelabel
  · exact F.sameMPV₂_weightedCanonicalBlock_commonFlat_of_reindexed μ hRelabel
  · intro x
    exact F.commonFlatWeight_ne_zero μ hμ x

/-- The one-sided zero-tail equation, weighted nonzero-part equality, and nonvanishing
of transported common-sector weights obtained from the coordinate-grouping condition. -/
lemma zeroTail_commonFlat_transport_of_groupedBlockCastAgrees
    {d D r z : ℕ} {dim : Fin r → ℕ}
    (A : MPSTensor d D) (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (F : CommonBlockedCyclicSectorFamily blocks)
    (hμ : ∀ k, μ k ≠ 0)
    (hMPV : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv A σ = mpv (zeroMPSTensor d z) σ +
        mpv (toTensorFromBlocks (d := d) (μ := μ) blocks) σ)
    (hCast : ∀ k : Fin r, F.groupedBlockCastAgrees k) :
    (∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d F.p)),
      mpv (blockTensor (d := d) (D := D) A F.p) σ =
        mpv (zeroMPSTensor (blockPhysDim d F.p) z) σ +
          mpv (toTensorFromBlocks (d := blockPhysDim d F.p)
            (μ := F.commonFlatWeight μ) F.commonFlatBlocks) σ) ∧
    SameMPV₂
      (toTensorFromBlocks (d := blockPhysDim d F.p)
        (μ := fun k : Fin r => (μ k) ^ F.p)
        (fun k => blockTensor (d := d) (D := dim k) (blocks k) F.p))
      (toTensorFromBlocks (d := blockPhysDim d F.p)
        (μ := F.commonFlatWeight μ) F.commonFlatBlocks) ∧
    (∀ x, F.commonFlatWeight μ x ≠ 0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact zeroTail_commonFlat_of_groupedBlockCastAgrees A μ blocks F hMPV hCast
  · exact F.sameMPV₂_weightedCanonicalBlock_commonFlat_of_groupedBlockCastAgrees μ hCast
  · intro x
    exact F.commonFlatWeight_ne_zero μ hμ x

/-- The one-sided blocked-word relabeling hypothesis for cyclic-sector data.

It says that, for every common cyclic-sector family, the canonically blocked
weighted nonzero tensor agrees as an MPV family with the same blocks read through
the explicit relabeling of blocked physical words. This is the hypothesis isolated
by the current blocked-word coordinate problem. -/
abbrev CommonSectorRelabelingHypothesis (d : ℕ) : Prop :=
  ∀ {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (blocks : (k : Fin r) → MPSTensor d (dim k))
    (F : CommonBlockedCyclicSectorFamily blocks),
    SameMPV₂
      (toTensorFromBlocks (d := blockPhysDim d F.p)
        (μ := fun k : Fin r => (μ k) ^ F.p)
        (fun k => blockTensor (d := d) (D := dim k) (blocks k) F.p))
      (toTensorFromBlocks (d := blockPhysDim d F.p)
        (μ := fun k : Fin r => (μ k) ^ F.p) F.commonReindexedBlock)

/-- The global coordinate-grouping assertion for common cyclic-sector families.

It requires every common blocked cyclic-sector family to satisfy the
coordinate-grouping condition for each original block, so the canonical identification
with the iterated blocked alphabet is the explicit grouping of direct blocked words. -/
abbrev CommonGroupedBlockCastHypothesis (d : ℕ) : Prop :=
  ∀ {r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (F : CommonBlockedCyclicSectorFamily blocks),
    ∀ k : Fin r, F.groupedBlockCastAgrees k

namespace CommonGroupedBlockCastHypothesis

/-- The canonical coordinate grouping for common blocked cyclic-sector families. -/
theorem of_flattenWordOfBlock_cast_eq (d : ℕ) : CommonGroupedBlockCastHypothesis d := by
  intro r dim blocks F k
  exact F.groupedBlockCastAgrees_of_flattenWordOfBlock_cast_eq
    (fun hp_eq h_card i =>
      CommonBlockedCyclicSectorFamily.flattenWordOfBlock_cast_eq hp_eq h_card i) k

/-- The coordinate-grouping assertion implies the one-sided reindexing hypothesis
used by the common-sector structural theorem. -/
theorem toRelabelingHypothesis {d : ℕ}
    (hCast : CommonGroupedBlockCastHypothesis d) :
    CommonSectorRelabelingHypothesis d := by
  intro r dim μ blocks F
  exact F.sameMPV₂_weightedCanonicalBlock_commonReindexedBlock_of_groupedBlockCastAgrees μ
    (hCast blocks F)

end CommonGroupedBlockCastHypothesis

set_option maxHeartbeats 800000 in
-- The conclusion records both decompositions and all their structural hypotheses together.
/-- **Common primitive irreducible block decompositions after blocked-word reindexing.**

Assume the one-sided equality which identifies, for every common cyclic-sector
family, the canonically blocked weighted nonzero part with the same family written
using the reindexing of blocked physical words.  Then two tensors with the same
MPV family have one common positive blocking length whose nonzero parts are
weighted families of trace-preserving, primitive, tensor-irreducible blocks with
positive bond dimensions and nonzero weights.  The zero-tail equations are stated
at that same blocking length, and the two nonzero parts agree at all positive
lengths, with the length-zero zero-tail identity recorded separately.

The displayed reindexing equality is the remaining one-sided blocked-word
theorem; this result isolates the mathematical hypotheses used before the later
injectivity and BNT comparison. -/
theorem afterBlocking_commonPrimitiveIrreducibleBlocks_of_reindexedNonzeroParts
    {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B)
    (hReindexed : CommonSectorRelabelingHypothesis d) :
    ∃ p : ℕ, 0 < p ∧
    ∃ (zeroTailA zeroTailB : ℕ),
    ∃ (rA : ℕ) (dimA : Fin rA → ℕ) (μA : Fin rA → ℂ)
      (blocksA : (x : Fin rA) → MPSTensor (blockPhysDim d p) (dimA x)),
    ∃ (rB : ℕ) (dimB : Fin rB → ℕ) (μB : Fin rB → ℂ)
      (blocksB : (x : Fin rB) → MPSTensor (blockPhysDim d p) (dimB x)),
      (∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d p)),
        mpv (blockTensor (d := d) (D := D₁) A p) σ =
          mpv (zeroMPSTensor (blockPhysDim d p) zeroTailA) σ +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) σ) ∧
      (∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d p)),
        mpv (blockTensor (d := d) (D := D₂) B p) σ =
          mpv (zeroMPSTensor (blockPhysDim d p) zeroTailB) σ +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) σ) ∧
      SameMPV₂Pos (blockTensor (d := d) (D := D₁) A p)
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) ∧
      SameMPV₂Pos (blockTensor (d := d) (D := D₂) B p)
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) ∧
      SameMPV₂Pos
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA)
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) ∧
      (∀ σ : Fin 0 → Fin (blockPhysDim d p),
        (zeroTailA : ℂ) +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) σ =
          (zeroTailB : ℂ) +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) σ) ∧
      (∀ x, μA x ≠ 0) ∧
      (∀ x, μB x ≠ 0) ∧
      (∀ x, ∑ i : Fin (blockPhysDim d p), (blocksA x i)ᴴ * blocksA x i = 1) ∧
      (∀ x, ∑ i : Fin (blockPhysDim d p), (blocksB x i)ᴴ * blocksB x i = 1) ∧
      (∀ x, _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := dimA x) (blocksA x))) ∧
      (∀ x, _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := dimB x) (blocksB x))) ∧
      (∀ x, IsIrreducibleTensor (blocksA x)) ∧
      (∀ x, IsIrreducibleTensor (blocksB x)) ∧
      (∀ x, 0 < dimA x) ∧
      (∀ x, 0 < dimB x) := by
  obtain ⟨p, hp, zeroTailA, rA₀, dimA₀, μA₀, blocksA₀,
      zeroTailB, rB₀, dimB₀, μB₀, blocksB₀, familyA, familyB,
      hFamilyA, hFamilyB, hZA, hZB, hPosCanon, hZeroCanon,
      _hReindexedA, _hReindexedB, hμA, hμB, hTPA, hTPB, hPrimA, hPrimB,
      hIrrA, hIrrB, hDimA, hDimB⟩ :=
    afterBlocking_commonLengthCommonSectorData_of_sameMPV₂ A B hSame
  have hWordA := hReindexed μA₀ blocksA₀ familyA
  have hWordB := hReindexed μB₀ blocksB₀ familyB
  have hFlatA_raw := familyA.sameMPV₂_weightedCanonicalBlock_commonFlat_of_reindexed μA₀ hWordA
  have hFlatB_raw := familyB.sameMPV₂_weightedCanonicalBlock_commonFlat_of_reindexed μB₀ hWordB
  let flatBlocksA : (x : Fin (∑ k : Fin rA₀, familyA.period k)) →
      MPSTensor (blockPhysDim d p) (familyA.commonFlatDim x) :=
    fun x => cast (congr_arg (fun q => MPSTensor (blockPhysDim d q)
      (familyA.commonFlatDim x)) hFamilyA) (familyA.commonFlatBlocks x)
  let flatBlocksB : (x : Fin (∑ k : Fin rB₀, familyB.period k)) →
      MPSTensor (blockPhysDim d p) (familyB.commonFlatDim x) :=
    fun x => cast (congr_arg (fun q => MPSTensor (blockPhysDim d q)
      (familyB.commonFlatDim x)) hFamilyB) (familyB.commonFlatBlocks x)
  let nonzeroA := toTensorFromBlocks (d := blockPhysDim d p)
    (μ := familyA.commonFlatWeight μA₀) flatBlocksA
  let nonzeroB := toTensorFromBlocks (d := blockPhysDim d p)
    (μ := familyB.commonFlatWeight μB₀) flatBlocksB
  have hFlatA : SameMPV₂
      (toTensorFromBlocks (d := blockPhysDim d p)
        (μ := fun k : Fin rA₀ => (μA₀ k) ^ p)
        (fun k => blockTensor (d := d) (D := dimA₀ k) (blocksA₀ k) p))
      nonzeroA := by
    cases hFamilyA
    simpa [flatBlocksA, nonzeroA] using hFlatA_raw
  have hFlatB : SameMPV₂
      (toTensorFromBlocks (d := blockPhysDim d p)
        (μ := fun k : Fin rB₀ => (μB₀ k) ^ p)
        (fun k => blockTensor (d := d) (D := dimB₀ k) (blocksB₀ k) p))
      nonzeroB := by
    cases hFamilyB
    simpa [flatBlocksB, nonzeroB] using hFlatB_raw
  have hZAflat : ∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d p)),
      mpv (blockTensor (d := d) (D := D₁) A p) σ =
        mpv (zeroMPSTensor (blockPhysDim d p) zeroTailA) σ +
          mpv nonzeroA σ := by
    intro N σ
    calc
      mpv (blockTensor (d := d) (D := D₁) A p) σ =
          mpv (zeroMPSTensor (blockPhysDim d p) zeroTailA) σ +
            mpv (toTensorFromBlocks (d := blockPhysDim d p)
              (fun k : Fin rA₀ => (μA₀ k) ^ p)
              (fun k => blockTensor (d := d) (D := dimA₀ k) (blocksA₀ k) p)) σ :=
        hZA N σ
      _ = mpv (zeroMPSTensor (blockPhysDim d p) zeroTailA) σ + mpv nonzeroA σ := by
        rw [hFlatA N σ]
  have hZBflat : ∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d p)),
      mpv (blockTensor (d := d) (D := D₂) B p) σ =
        mpv (zeroMPSTensor (blockPhysDim d p) zeroTailB) σ +
          mpv nonzeroB σ := by
    intro N σ
    calc
      mpv (blockTensor (d := d) (D := D₂) B p) σ =
          mpv (zeroMPSTensor (blockPhysDim d p) zeroTailB) σ +
            mpv (toTensorFromBlocks (d := blockPhysDim d p)
              (fun k : Fin rB₀ => (μB₀ k) ^ p)
              (fun k => blockTensor (d := d) (D := dimB₀ k) (blocksB₀ k) p)) σ :=
        hZB N σ
      _ = mpv (zeroMPSTensor (blockPhysDim d p) zeroTailB) σ + mpv nonzeroB σ := by
        rw [hFlatB N σ]
  have hAPos : SameMPV₂Pos (blockTensor (d := d) (D := D₁) A p) nonzeroA := by
    intro N hN σ
    have hZero : mpv (zeroMPSTensor (blockPhysDim d p) zeroTailA) σ = 0 := by
      rw [mpv_zeroMPSTensor]
      simp [Nat.ne_of_gt hN]
    calc
      mpv (blockTensor (d := d) (D := D₁) A p) σ =
          mpv (zeroMPSTensor (blockPhysDim d p) zeroTailA) σ + mpv nonzeroA σ :=
        hZAflat N σ
      _ = mpv nonzeroA σ := by rw [hZero]; simp
  have hBPos : SameMPV₂Pos (blockTensor (d := d) (D := D₂) B p) nonzeroB := by
    intro N hN σ
    have hZero : mpv (zeroMPSTensor (blockPhysDim d p) zeroTailB) σ = 0 := by
      rw [mpv_zeroMPSTensor]
      simp [Nat.ne_of_gt hN]
    calc
      mpv (blockTensor (d := d) (D := D₂) B p) σ =
          mpv (zeroMPSTensor (blockPhysDim d p) zeroTailB) σ + mpv nonzeroB σ :=
        hZBflat N σ
      _ = mpv nonzeroB σ := by rw [hZero]; simp
  have hNonzeroPos : SameMPV₂Pos nonzeroA nonzeroB := by
    intro N hN σ
    calc
      mpv nonzeroA σ =
          mpv (toTensorFromBlocks (d := blockPhysDim d p)
            (fun k : Fin rA₀ => (μA₀ k) ^ p)
            (fun k => blockTensor (d := d) (D := dimA₀ k) (blocksA₀ k) p)) σ :=
        (hFlatA N σ).symm
      _ = mpv (toTensorFromBlocks (d := blockPhysDim d p)
            (fun k : Fin rB₀ => (μB₀ k) ^ p)
            (fun k => blockTensor (d := d) (D := dimB₀ k) (blocksB₀ k) p)) σ :=
        hPosCanon N hN σ
      _ = mpv nonzeroB σ := hFlatB N σ
  have hZeroFlat : ∀ σ : Fin 0 → Fin (blockPhysDim d p),
      (zeroTailA : ℂ) + mpv nonzeroA σ = (zeroTailB : ℂ) + mpv nonzeroB σ := by
    intro σ
    calc
      (zeroTailA : ℂ) + mpv nonzeroA σ =
          (zeroTailA : ℂ) +
            mpv (toTensorFromBlocks (d := blockPhysDim d p)
              (fun k : Fin rA₀ => (μA₀ k) ^ p)
              (fun k => blockTensor (d := d) (D := dimA₀ k) (blocksA₀ k) p)) σ := by
        rw [← hFlatA 0 σ]
      _ = (zeroTailB : ℂ) +
            mpv (toTensorFromBlocks (d := blockPhysDim d p)
              (fun k : Fin rB₀ => (μB₀ k) ^ p)
              (fun k => blockTensor (d := d) (D := dimB₀ k) (blocksB₀ k) p)) σ :=
        hZeroCanon σ
      _ = (zeroTailB : ℂ) + mpv nonzeroB σ := by
        rw [hFlatB 0 σ]
  have hTPA' : ∀ x,
      ∑ i : Fin (blockPhysDim d p), (flatBlocksA x i)ᴴ * flatBlocksA x i = 1 := by
    intro x
    cases hFamilyA
    simpa [flatBlocksA] using hTPA x
  have hTPB' : ∀ x,
      ∑ i : Fin (blockPhysDim d p), (flatBlocksB x i)ᴴ * flatBlocksB x i = 1 := by
    intro x
    cases hFamilyB
    simpa [flatBlocksB] using hTPB x
  have hPrimA' : ∀ x, _root_.IsPrimitive
      (transferMap (d := blockPhysDim d p) (D := familyA.commonFlatDim x) (flatBlocksA x)) := by
    intro x
    cases hFamilyA
    simpa [flatBlocksA] using hPrimA x
  have hPrimB' : ∀ x, _root_.IsPrimitive
      (transferMap (d := blockPhysDim d p) (D := familyB.commonFlatDim x) (flatBlocksB x)) := by
    intro x
    cases hFamilyB
    simpa [flatBlocksB] using hPrimB x
  have hIrrA' : ∀ x, IsIrreducibleTensor (flatBlocksA x) := by
    intro x
    cases hFamilyA
    simpa [flatBlocksA] using hIrrA x
  have hIrrB' : ∀ x, IsIrreducibleTensor (flatBlocksB x) := by
    intro x
    cases hFamilyB
    simpa [flatBlocksB] using hIrrB x
  refine ⟨p, hp, zeroTailA, zeroTailB,
    (∑ k : Fin rA₀, familyA.period k), familyA.commonFlatDim, familyA.commonFlatWeight μA₀,
    flatBlocksA,
    (∑ k : Fin rB₀, familyB.period k), familyB.commonFlatDim, familyB.commonFlatWeight μB₀,
    flatBlocksB,
    hZAflat, hZBflat, hAPos, hBPos, hNonzeroPos, hZeroFlat,
    hμA, hμB, hTPA', hTPB', hPrimA', hPrimB', hIrrA', hIrrB', hDimA, hDimB⟩

/-- **Unconditional common primitive irreducible block decompositions.**

The proved blocked-word flattening identity supplies the grouped-cast hypothesis needed to
apply `afterBlocking_commonPrimitiveIrreducibleBlocks_of_reindexedNonzeroParts` without any
blocking-coordinate hypothesis.

The proof chains:
1. `flattenWordOfBlock_cast_eq` → `CommonGroupedBlockCastHypothesis d`
   (via `groupedBlockCastAgrees_of_flattenWordOfBlock_cast_eq`)
2. `CommonGroupedBlockCastHypothesis d` → `CommonSectorRelabelingHypothesis d`
   (via `CommonGroupedBlockCastHypothesis.toRelabelingHypothesis`)
3. `CommonSectorRelabelingHypothesis d` → the full common-block decomposition
   (via `afterBlocking_commonPrimitiveIrreducibleBlocks_of_reindexedNonzeroParts`)
-/
theorem unconditional_commonPrimitiveIrreducibleBlocks
    {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B) :
    ∃ p : ℕ, 0 < p ∧
    ∃ (zeroTailA zeroTailB : ℕ),
    ∃ (rA : ℕ) (dimA : Fin rA → ℕ) (μA : Fin rA → ℂ)
      (blocksA : (x : Fin rA) → MPSTensor (blockPhysDim d p) (dimA x)),
    ∃ (rB : ℕ) (dimB : Fin rB → ℕ) (μB : Fin rB → ℂ)
      (blocksB : (x : Fin rB) → MPSTensor (blockPhysDim d p) (dimB x)),
      (∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d p)),
        mpv (blockTensor (d := d) (D := D₁) A p) σ =
          mpv (zeroMPSTensor (blockPhysDim d p) zeroTailA) σ +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) σ) ∧
      (∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d p)),
        mpv (blockTensor (d := d) (D := D₂) B p) σ =
          mpv (zeroMPSTensor (blockPhysDim d p) zeroTailB) σ +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) σ) ∧
      SameMPV₂Pos (blockTensor (d := d) (D := D₁) A p)
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) ∧
      SameMPV₂Pos (blockTensor (d := d) (D := D₂) B p)
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) ∧
      SameMPV₂Pos
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA)
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) ∧
      (∀ σ : Fin 0 → Fin (blockPhysDim d p),
        (zeroTailA : ℂ) +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) σ =
          (zeroTailB : ℂ) +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) σ) ∧
      (∀ x, μA x ≠ 0) ∧
      (∀ x, μB x ≠ 0) ∧
      (∀ x, ∑ i : Fin (blockPhysDim d p), (blocksA x i)ᴴ * blocksA x i = 1) ∧
      (∀ x, ∑ i : Fin (blockPhysDim d p), (blocksB x i)ᴴ * blocksB x i = 1) ∧
      (∀ x, _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := dimA x) (blocksA x))) ∧
      (∀ x, _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := dimB x) (blocksB x))) ∧
      (∀ x, IsIrreducibleTensor (blocksA x)) ∧
      (∀ x, IsIrreducibleTensor (blocksB x)) ∧
      (∀ x, 0 < dimA x) ∧
      (∀ x, 0 < dimB x) := by
  have h_group : CommonGroupedBlockCastHypothesis d :=
    CommonGroupedBlockCastHypothesis.of_flattenWordOfBlock_cast_eq d
  have h_relabel : CommonSectorRelabelingHypothesis d :=
    h_group.toRelabelingHypothesis
  exact afterBlocking_commonPrimitiveIrreducibleBlocks_of_reindexedNonzeroParts
    A B hSame h_relabel

end MPSTensor

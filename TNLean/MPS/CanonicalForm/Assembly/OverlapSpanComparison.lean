/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.Assembly.BasicSectorComparison

open scoped Matrix BigOperators ComplexOrder MatrixOrder


/-!
# Sector-basis overlap-span hypotheses from common primitive data

This module collects the overlap-span hypotheses produced from the common primitive
nonzero-sector families obtained after blocked-word reindexing. It keeps the span,
common phase-cover, BNT-cover, explicit BNT-data, and proportional-comparison variants
in one place, while leaving the final sector-comparison reformulations in
`TNLean.MPS.CanonicalForm.Assembly.ProportionalComparison`.

## References

* [Cirac-Perez-Garcia-Schuch-Verstraete, arXiv:1606.00608, Section 2.3 + Appendix A]
* [Cirac-Perez-Garcia-Schuch-Verstraete, arXiv:2011.12127, Section IV]

## Tags

matrix product states, canonical form, BNT, overlap spans
-/

namespace MPSTensor

/-- **One-sided BNT overlap-orthogonality data from reindexed nonzero sectors.**

The common primitive irreducible block theorem supplies the final nonzero-sector
families after the chosen blocking and blocked-word reindexing. Applying the
phase-class BNT construction separately to the two families gives sector bases
with positive dimensions, left-canonical normalization, self-overlap limit `1`,
and off-overlap limit `0` for distinct representatives.

This theorem deliberately stops before the two-family finite-length span
comparison and one-site injectivity inputs. Those are the remaining data needed
to upgrade the one-sided overlap-orthogonality hypotheses to
`SectorBasisOverlapSpanHypotheses`. -/
theorem sectorBasisOverlapOrthoHypotheses_of_reindexedNonzeroParts
    {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B)
    (hReindexed : CommonSectorRelabelingHypothesis d) :
    ∃ p : ℕ, 0 < p ∧
    ∃ P Q : SectorDecomposition (blockPhysDim d p),
      SameMPV₂Pos (blockTensor (d := d) (D := D₁) A p) P.toTensor ∧
      SameMPV₂Pos (blockTensor (d := d) (D := D₂) B p) Q.toTensor ∧
      HasBNTSectorData P ∧ HasBNTSectorData Q ∧
      SectorBasisOverlapOrthoHypotheses P ∧
      SectorBasisOverlapOrthoHypotheses Q := by
  obtain ⟨p, hp, zeroTailA, zeroTailB, rA, dimA, μA, blocksA,
      rB, dimB, μB, blocksB, _hAblocks, _hBblocks, hAPos, hBPos, _hNonzeroPos,
      _hZero, hμA, hμB, hTPA, hTPB, hPrimA, hPrimB, hIrrA, hIrrB, hDimA, hDimB⟩ :=
    afterBlocking_commonPrimitiveIrreducibleBlocks_of_reindexedNonzeroParts A B hSame hReindexed
  letI : ∀ x : Fin rA, NeZero (dimA x) := fun x => ⟨Nat.ne_of_gt (hDimA x)⟩
  letI : ∀ x : Fin rB, NeZero (dimB x) := fun x => ⟨Nat.ne_of_gt (hDimB x)⟩
  let nonzeroA := toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA
  let nonzeroB := toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB
  obtain ⟨P, hPblocks, hPbnt, hPOrtho, _hPInj_of⟩ :=
    exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks_with_overlapOrtho
      (d := blockPhysDim d p) μA blocksA hTPA hIrrA hPrimA hμA
  obtain ⟨Q, hQblocks, hQbnt, hQOrtho, _hQInj_of⟩ :=
    exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks_with_overlapOrtho
      (d := blockPhysDim d p) μB blocksB hTPB hIrrB hPrimB hμB
  have hAP : SameMPV₂Pos (blockTensor (d := d) (D := D₁) A p) P.toTensor := by
    intro N hN σ
    calc
      mpv (blockTensor (d := d) (D := D₁) A p) σ = mpv nonzeroA σ := hAPos N hN σ
      _ = mpv P.toTensor σ := (hPblocks N σ).symm
  have hBQ : SameMPV₂Pos (blockTensor (d := d) (D := D₂) B p) Q.toTensor := by
    intro N hN σ
    calc
      mpv (blockTensor (d := d) (D := D₂) B p) σ = mpv nonzeroB σ := hBPos N hN σ
      _ = mpv Q.toTensor σ := (hQblocks N σ).symm
  exact ⟨p, hp, P, Q, hAP, hBQ, hPbnt, hQbnt, hPOrtho, hQOrtho⟩

/-- **Sector basis overlap-span data from common primitive nonzero-sector families.**

The common primitive irreducible block theorem supplies the two nonzero-sector decompositions
obtained after blocked-word reindexing. If the remaining zero-tail equality, one-site
injectivity, and finite-length span equality are supplied for those same families, the
collapsed BNT representative construction produces a pair of sector decompositions satisfying
`SectorBasisOverlapSpanHypotheses`.

This theorem isolates the `SectorBasisOverlapSpanHypotheses` construction used internally by
`afterBlocking_sectorComparison_zeroTail_of_reindexedNonzeroParts_spanHypotheses`. The
conclusion records the nonzero-block MPV agreements, the BNT linear-independence data, and
the eleven overlap-span fields: nonzero bond dimensions, injectivity, left-canonical
normalization, asymptotic self- and off-diagonal overlaps, and equality of the finite-length
MPV spans of the two sector bases.

The `hRemaining` function must supply `CommonPrimitiveSpanHypotheses` for the block families
produced by `afterBlocking_commonPrimitiveIrreducibleBlocks_of_reindexedNonzeroParts`.
Concretely it needs to prove equality of the two zero-tail dimensions, one-site injectivity
of the nonzero-weight blocks, and equality of their finite-length MPV spans. The last of
these can be supplied by a common MPV phase cover (via
`CommonPrimitiveSpanHypotheses.of_commonPhaseCover`) or by a BNT proportional-decomposition
comparison (via `CommonPrimitiveProportionalHypotheses.toSpanHypotheses`). -/
theorem sectorBasisOverlapSpanHypotheses_of_reindexedNonzeroParts
    {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B)
    (hReindexed : CommonSectorRelabelingHypothesis d)
    (hRemaining : ∀ {p zeroTailA zeroTailB rA rB : ℕ}
      {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
      {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
      {blocksA : (x : Fin rA) → MPSTensor (blockPhysDim d p) (dimA x)}
      {blocksB : (x : Fin rB) → MPSTensor (blockPhysDim d p) (dimB x)},
      0 < p →
      (∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d p)),
        mpv (blockTensor (d := d) (D := D₁) A p) σ =
          mpv (zeroMPSTensor (blockPhysDim d p) zeroTailA) σ +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) σ) →
      (∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d p)),
        mpv (blockTensor (d := d) (D := D₂) B p) σ =
          mpv (zeroMPSTensor (blockPhysDim d p) zeroTailB) σ +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) σ) →
      SameMPV₂Pos (blockTensor (d := d) (D := D₁) A p)
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) →
      SameMPV₂Pos (blockTensor (d := d) (D := D₂) B p)
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) →
      SameMPV₂Pos
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA)
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) →
      (∀ σ : Fin 0 → Fin (blockPhysDim d p),
        (zeroTailA : ℂ) +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) σ =
          (zeroTailB : ℂ) +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) σ) →
      (∀ x, μA x ≠ 0) →
      (∀ x, μB x ≠ 0) →
      (∀ x, ∑ i : Fin (blockPhysDim d p), (blocksA x i)ᴴ * blocksA x i = 1) →
      (∀ x, ∑ i : Fin (blockPhysDim d p), (blocksB x i)ᴴ * blocksB x i = 1) →
      (∀ x, _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := dimA x) (blocksA x))) →
      (∀ x, _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := dimB x) (blocksB x))) →
      (∀ x, IsIrreducibleTensor (blocksA x)) →
      (∀ x, IsIrreducibleTensor (blocksB x)) →
      (∀ x, 0 < dimA x) →
      (∀ x, 0 < dimB x) →
      CommonPrimitiveSpanHypotheses zeroTailA zeroTailB blocksA blocksB) :
    ∃ p : ℕ, 0 < p ∧
    ∃ P Q : SectorDecomposition (blockPhysDim d p),
      SameMPV₂ P.toTensor Q.toTensor ∧
      HasBNTSectorData P ∧ HasBNTSectorData Q ∧
      SectorBasisOverlapSpanHypotheses P Q := by
  obtain ⟨p, hp, zeroTailA, zeroTailB, rA, dimA, μA, blocksA,
      rB, dimB, μB, blocksB, hAblocks, hBblocks, hAPos, hBPos, hNonzeroPos,
      hZero, hμA, hμB, hTPA, hTPB, hPrimA, hPrimB, hIrrA, hIrrB, hDimA, hDimB⟩ :=
    afterBlocking_commonPrimitiveIrreducibleBlocks_of_reindexedNonzeroParts A B hSame hReindexed
  have hHyp : CommonPrimitiveSpanHypotheses zeroTailA zeroTailB blocksA blocksB :=
    hRemaining hp hAblocks hBblocks hAPos hBPos hNonzeroPos hZero hμA hμB hTPA hTPB
      hPrimA hPrimB hIrrA hIrrB hDimA hDimB
  letI : ∀ x : Fin rA, NeZero (dimA x) := fun x => ⟨Nat.ne_of_gt (hDimA x)⟩
  letI : ∀ x : Fin rB, NeZero (dimB x) := fun x => ⟨Nat.ne_of_gt (hDimB x)⟩
  let nonzeroA := toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA
  let nonzeroB := toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB
  have hAB : SameMPV₂ (blockTensor (d := d) (D := D₁) A p)
                      (blockTensor (d := d) (D := D₂) B p) :=
    sameMPV₂_blockTensor A B hSame p
  have hNonzero : SameMPV₂ nonzeroA nonzeroB :=
    sameMPV₂_live_of_sameMPV₂_with_zeroTail_eq
      (blockTensor (d := d) (D := D₁) A p)
      (blockTensor (d := d) (D := D₂) B p)
      nonzeroA nonzeroB hAB hAblocks hBblocks hHyp.zeroTail_eq
  obtain ⟨P, Q, hPblocks, hQblocks, hPbnt, hQbnt, hOverlapSpan⟩ :=
    exists_bnt_sectorDecomp_pair_with_overlapSpan_of_block_span_eq
      (d := blockPhysDim d p) μA blocksA μB blocksB hTPA hTPB hIrrA hIrrB
      hPrimA hPrimB hHyp.left_injective hHyp.right_injective hμA hμB hHyp.span_eq
  have hPQeq : SameMPV₂ P.toTensor Q.toTensor := by
    intro N σ
    calc
      mpv P.toTensor σ = mpv nonzeroA σ := hPblocks N σ
      _ = mpv nonzeroB σ := hNonzero N σ
      _ = mpv Q.toTensor σ := (hQblocks N σ).symm
  exact ⟨p, hp, P, Q, hPQeq, hPbnt, hQbnt, hOverlapSpan⟩

/-- **Sector basis overlap-span data via a common MPV phase cover.**

This is the common-phase-cover variant of
`sectorBasisOverlapSpanHypotheses_of_reindexedNonzeroParts`. Instead of requiring the
finite-length span equality directly, it asks for a common MPV phase cover of the two
nonzero-weight block families. The cover supplies the span equality through
`MPVCommonPhaseCover.span_eq`. -/
theorem sectorBasisOverlapSpanHypotheses_of_reindexedNonzeroParts_commonPhaseCover
    {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B)
    (hReindexed : CommonSectorRelabelingHypothesis d)
    (hRemaining : ∀ {p zeroTailA zeroTailB rA rB : ℕ}
      {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
      {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
      {blocksA : (x : Fin rA) → MPSTensor (blockPhysDim d p) (dimA x)}
      {blocksB : (x : Fin rB) → MPSTensor (blockPhysDim d p) (dimB x)},
      0 < p →
      (∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d p)),
        mpv (blockTensor (d := d) (D := D₁) A p) σ =
          mpv (zeroMPSTensor (blockPhysDim d p) zeroTailA) σ +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) σ) →
      (∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d p)),
        mpv (blockTensor (d := d) (D := D₂) B p) σ =
          mpv (zeroMPSTensor (blockPhysDim d p) zeroTailB) σ +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) σ) →
      SameMPV₂Pos (blockTensor (d := d) (D := D₁) A p)
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) →
      SameMPV₂Pos (blockTensor (d := d) (D := D₂) B p)
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) →
      SameMPV₂Pos
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA)
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) →
      (∀ σ : Fin 0 → Fin (blockPhysDim d p),
        (zeroTailA : ℂ) +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) σ =
          (zeroTailB : ℂ) +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) σ) →
      (∀ x, μA x ≠ 0) →
      (∀ x, μB x ≠ 0) →
      (∀ x, ∑ i : Fin (blockPhysDim d p), (blocksA x i)ᴴ * blocksA x i = 1) →
      (∀ x, ∑ i : Fin (blockPhysDim d p), (blocksB x i)ᴴ * blocksB x i = 1) →
      (∀ x, _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := dimA x) (blocksA x))) →
      (∀ x, _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := dimB x) (blocksB x))) →
      (∀ x, IsIrreducibleTensor (blocksA x)) →
      (∀ x, IsIrreducibleTensor (blocksB x)) →
      (∀ x, 0 < dimA x) →
      (∀ x, 0 < dimB x) →
      CommonPrimitivePhaseCoverHypotheses zeroTailA zeroTailB blocksA blocksB) :
    ∃ p : ℕ, 0 < p ∧
    ∃ P Q : SectorDecomposition (blockPhysDim d p),
      SameMPV₂ P.toTensor Q.toTensor ∧
      HasBNTSectorData P ∧ HasBNTSectorData Q ∧
      SectorBasisOverlapSpanHypotheses P Q := by
  obtain ⟨p, hp, zeroTailA, zeroTailB, rA, dimA, μA, blocksA,
      rB, dimB, μB, blocksB, hAblocks, hBblocks, hAPos, hBPos, hNonzeroPos,
      hZero, hμA, hμB, hTPA, hTPB, hPrimA, hPrimB, hIrrA, hIrrB, hDimA, hDimB⟩ :=
    afterBlocking_commonPrimitiveIrreducibleBlocks_of_reindexedNonzeroParts A B hSame hReindexed
  have hHyp : CommonPrimitivePhaseCoverHypotheses zeroTailA zeroTailB blocksA blocksB :=
    hRemaining hp hAblocks hBblocks hAPos hBPos hNonzeroPos hZero hμA hμB hTPA hTPB
      hPrimA hPrimB hIrrA hIrrB hDimA hDimB
  have hSpanHyp : CommonPrimitiveSpanHypotheses zeroTailA zeroTailB blocksA blocksB :=
    hHyp.toSpanHypotheses
  letI : ∀ x : Fin rA, NeZero (dimA x) := fun x => ⟨Nat.ne_of_gt (hDimA x)⟩
  letI : ∀ x : Fin rB, NeZero (dimB x) := fun x => ⟨Nat.ne_of_gt (hDimB x)⟩
  let nonzeroA := toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA
  let nonzeroB := toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB
  have hAB : SameMPV₂ (blockTensor (d := d) (D := D₁) A p)
                      (blockTensor (d := d) (D := D₂) B p) :=
    sameMPV₂_blockTensor A B hSame p
  have hNonzero : SameMPV₂ nonzeroA nonzeroB :=
    sameMPV₂_live_of_sameMPV₂_with_zeroTail_eq
      (blockTensor (d := d) (D := D₁) A p)
      (blockTensor (d := d) (D := D₂) B p)
      nonzeroA nonzeroB hAB hAblocks hBblocks hSpanHyp.zeroTail_eq
  obtain ⟨P, Q, hPblocks, hQblocks, hPbnt, hQbnt, hOverlapSpan⟩ :=
    exists_bnt_sectorDecomp_pair_with_overlapSpan_of_block_span_eq
      (d := blockPhysDim d p) μA blocksA μB blocksB hTPA hTPB hIrrA hIrrB
      hPrimA hPrimB hSpanHyp.left_injective hSpanHyp.right_injective hμA hμB hSpanHyp.span_eq
  have hPQeq : SameMPV₂ P.toTensor Q.toTensor := by
    intro N σ
    calc
      mpv P.toTensor σ = mpv nonzeroA σ := hPblocks N σ
      _ = mpv nonzeroB σ := hNonzero N σ
      _ = mpv Q.toTensor σ := (hQblocks N σ).symm
  exact ⟨p, hp, P, Q, hPQeq, hPbnt, hQbnt, hOverlapSpan⟩

/-- **Sector basis overlap-span data via BNT-cover hypotheses.**

This is the BNT-cover variant of
`sectorBasisOverlapSpanHypotheses_of_reindexedNonzeroParts_commonPhaseCover`.
The remaining input provides the BNT-level data for the produced nonzero-sector
families, with whatever total dimensions support the proportional-decomposition
data. The conversion from BNT-cover hypotheses to common primitive phase-cover
hypotheses then lets the common-phase-cover theorem supply the overlap-span data. -/
theorem sectorBasisOverlapSpanHypotheses_of_reindexedNonzeroParts_bntCover
    {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B)
    (hReindexed : CommonSectorRelabelingHypothesis d)
    (hRemaining : ∀ {p zeroTailA zeroTailB rA rB : ℕ}
      {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
      [∀ x : Fin rA, NeZero (dimA x)]
      [∀ x : Fin rB, NeZero (dimB x)]
      {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
      {blocksA : (x : Fin rA) → MPSTensor (blockPhysDim d p) (dimA x)}
      {blocksB : (x : Fin rB) → MPSTensor (blockPhysDim d p) (dimB x)},
      0 < p →
      (∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d p)),
        mpv (blockTensor (d := d) (D := D₁) A p) σ =
          mpv (zeroMPSTensor (blockPhysDim d p) zeroTailA) σ +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) σ) →
      (∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d p)),
        mpv (blockTensor (d := d) (D := D₂) B p) σ =
          mpv (zeroMPSTensor (blockPhysDim d p) zeroTailB) σ +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) σ) →
      SameMPV₂Pos (blockTensor (d := d) (D := D₁) A p)
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) →
      SameMPV₂Pos (blockTensor (d := d) (D := D₂) B p)
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) →
      SameMPV₂Pos
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA)
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) →
      (∀ σ : Fin 0 → Fin (blockPhysDim d p),
        (zeroTailA : ℂ) +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) σ =
          (zeroTailB : ℂ) +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) σ) →
      (∀ x, μA x ≠ 0) →
      (∀ x, μB x ≠ 0) →
      (∀ x, ∑ i : Fin (blockPhysDim d p), (blocksA x i)ᴴ * blocksA x i = 1) →
      (∀ x, ∑ i : Fin (blockPhysDim d p), (blocksB x i)ᴴ * blocksB x i = 1) →
      (∀ x, _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := dimA x) (blocksA x))) →
      (∀ x, _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := dimB x) (blocksB x))) →
      (∀ x, IsIrreducibleTensor (blocksA x)) →
      (∀ x, IsIrreducibleTensor (blocksB x)) →
      (∀ x, 0 < dimA x) →
      (∀ x, 0 < dimB x) →
      ∃ DtotA DtotB,
        Nonempty
          (CommonPrimitiveBNTCoverHypotheses (zeroTailA := zeroTailA) (zeroTailB := zeroTailB)
            (DtotA := DtotA) (DtotB := DtotB) μA μB blocksA blocksB)) :
    ∃ p : ℕ, 0 < p ∧
    ∃ P Q : SectorDecomposition (blockPhysDim d p),
      SameMPV₂ P.toTensor Q.toTensor ∧
      HasBNTSectorData P ∧ HasBNTSectorData Q ∧
      SectorBasisOverlapSpanHypotheses P Q := by
  refine sectorBasisOverlapSpanHypotheses_of_reindexedNonzeroParts_commonPhaseCover
    A B hSame hReindexed ?_
  intro p zeroTailA zeroTailB rA rB dimA dimB μA μB blocksA blocksB hp
    hAblocks hBblocks hAPos hBPos hNonzeroPos hZero hμA hμB hTPA hTPB hPrimA hPrimB
    hIrrA hIrrB hDimA hDimB
  letI : ∀ x : Fin rA, NeZero (dimA x) := fun x => ⟨Nat.ne_of_gt (hDimA x)⟩
  letI : ∀ x : Fin rB, NeZero (dimB x) := fun x => ⟨Nat.ne_of_gt (hDimB x)⟩
  obtain ⟨DtotA, DtotB, ⟨hBNTCover⟩⟩ :=
    hRemaining hp hAblocks hBblocks hAPos hBPos hNonzeroPos hZero hμA hμB hTPA hTPB
      hPrimA hPrimB hIrrA hIrrB hDimA hDimB
  exact hBNTCover.toCommonPrimitivePhaseCoverHypotheses

/-- **Sector basis overlap-span data from explicit common primitive BNT data.**

This is the explicit-data variant of
`sectorBasisOverlapSpanHypotheses_of_reindexedNonzeroParts_bntCover`. It forms the
BNT-cover hypotheses from the common primitive structural data together with the
remaining BNT comparison inputs, then applies the BNT-cover overlap-span theorem. -/
theorem sectorBasisOverlapSpanHypotheses_of_commonPrimitiveBNTData
    {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B)
    (hReindexed : CommonSectorRelabelingHypothesis d)
    (hRemaining : ∀ {p zeroTailA zeroTailB rA rB : ℕ}
      {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
      [∀ x : Fin rA, NeZero (dimA x)]
      [∀ x : Fin rB, NeZero (dimB x)]
      {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
      {blocksA : (x : Fin rA) → MPSTensor (blockPhysDim d p) (dimA x)}
      {blocksB : (x : Fin rB) → MPSTensor (blockPhysDim d p) (dimB x)},
      0 < p →
      (∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d p)),
        mpv (blockTensor (d := d) (D := D₁) A p) σ =
          mpv (zeroMPSTensor (blockPhysDim d p) zeroTailA) σ +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) σ) →
      (∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d p)),
        mpv (blockTensor (d := d) (D := D₂) B p) σ =
          mpv (zeroMPSTensor (blockPhysDim d p) zeroTailB) σ +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) σ) →
      SameMPV₂Pos (blockTensor (d := d) (D := D₁) A p)
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) →
      SameMPV₂Pos (blockTensor (d := d) (D := D₂) B p)
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) →
      SameMPV₂Pos
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA)
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) →
      (∀ σ : Fin 0 → Fin (blockPhysDim d p),
        (zeroTailA : ℂ) +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) σ =
          (zeroTailB : ℂ) +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) σ) →
      (∀ x, μA x ≠ 0) →
      (∀ x, μB x ≠ 0) →
      (∀ x, ∑ i : Fin (blockPhysDim d p), (blocksA x i)ᴴ * blocksA x i = 1) →
      (∀ x, ∑ i : Fin (blockPhysDim d p), (blocksB x i)ᴴ * blocksB x i = 1) →
      (∀ x, _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := dimA x) (blocksA x))) →
      (∀ x, _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := dimB x) (blocksB x))) →
      (∀ x, IsIrreducibleTensor (blocksA x)) →
      (∀ x, IsIrreducibleTensor (blocksB x)) →
      (∀ x, 0 < dimA x) →
      (∀ x, 0 < dimB x) →
      Σ DtotA : ℕ, Σ DtotB : ℕ,
        { _hDecomp : ProportionalDecompositionData (d := blockPhysDim d p)
            blocksA blocksB DtotA DtotB //
          StrictAnti (fun x : Fin rA => ‖μA x‖) ∧
          StrictAnti (fun x : Fin rB => ‖μB x‖) ∧
          BlocksNotGaugePhaseEquiv (d := blockPhysDim d p) blocksA ∧
          BlocksNotGaugePhaseEquiv (d := blockPhysDim d p) blocksB ∧
          zeroTailA = zeroTailB ∧
          (∀ x, IsInjective (blocksA x)) ∧
          (∀ x, IsInjective (blocksB x)) }) :
    ∃ p : ℕ, 0 < p ∧
    ∃ P Q : SectorDecomposition (blockPhysDim d p),
      SameMPV₂ P.toTensor Q.toTensor ∧
      HasBNTSectorData P ∧ HasBNTSectorData Q ∧
      SectorBasisOverlapSpanHypotheses P Q := by
  refine sectorBasisOverlapSpanHypotheses_of_reindexedNonzeroParts_bntCover
    A B hSame hReindexed ?_
  intro p zeroTailA zeroTailB rA rB dimA dimB _ _ μA μB blocksA blocksB hp
    hAblocks hBblocks hAPos hBPos hNonzeroPos hZero hμA hμB hTPA hTPB hPrimA hPrimB
    hIrrA hIrrB hDimA hDimB
  obtain ⟨DtotA, DtotB, hPacked⟩ :=
    hRemaining hp hAblocks hBblocks hAPos hBPos hNonzeroPos hZero hμA hμB hTPA hTPB
      hPrimA hPrimB hIrrA hIrrB hDimA hDimB
  rcases hPacked.2 with
    ⟨hAntiA, hAntiB, hNotGpeA, hNotGpeB, hZeroTail, hInjA, hInjB⟩
  refine ⟨DtotA, DtotB, ⟨?_⟩⟩
  exact CommonPrimitiveBNTCoverHypotheses.ofCommonPrimitiveData
    hμA hμB hTPA hTPB hPrimA hPrimB hIrrA hIrrB hAntiA hAntiB hNotGpeA hNotGpeB
    hZeroTail hInjA hInjB hPacked.1

/-- **Sector basis overlap-span data from explicit common primitive BNT data,
deriving the zero-tail identity.**

This variant of `sectorBasisOverlapSpanHypotheses_of_commonPrimitiveBNTData`
removes the explicit zero-tail equality from the remaining data. The identity is
derived from the length-zero MPV equality and proportional-decomposition data. -/
theorem sectorBasisOverlapSpanHypotheses_of_commonPrimitiveBNTData_zeroTailIdentity
    {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B)
    (hReindexed : CommonSectorRelabelingHypothesis d)
    (hRemaining : ∀ {p zeroTailA zeroTailB rA rB : ℕ}
      {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
      [∀ x : Fin rA, NeZero (dimA x)]
      [∀ x : Fin rB, NeZero (dimB x)]
      {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
      {blocksA : (x : Fin rA) → MPSTensor (blockPhysDim d p) (dimA x)}
      {blocksB : (x : Fin rB) → MPSTensor (blockPhysDim d p) (dimB x)},
      0 < p →
      (∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d p)),
        mpv (blockTensor (d := d) (D := D₁) A p) σ =
          mpv (zeroMPSTensor (blockPhysDim d p) zeroTailA) σ +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) σ) →
      (∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d p)),
        mpv (blockTensor (d := d) (D := D₂) B p) σ =
          mpv (zeroMPSTensor (blockPhysDim d p) zeroTailB) σ +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) σ) →
      SameMPV₂Pos (blockTensor (d := d) (D := D₁) A p)
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) →
      SameMPV₂Pos (blockTensor (d := d) (D := D₂) B p)
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) →
      SameMPV₂Pos
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA)
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) →
      (∀ σ : Fin 0 → Fin (blockPhysDim d p),
        (zeroTailA : ℂ) +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) σ =
          (zeroTailB : ℂ) +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) σ) →
      (∀ x, μA x ≠ 0) →
      (∀ x, μB x ≠ 0) →
      (∀ x, ∑ i : Fin (blockPhysDim d p), (blocksA x i)ᴴ * blocksA x i = 1) →
      (∀ x, ∑ i : Fin (blockPhysDim d p), (blocksB x i)ᴴ * blocksB x i = 1) →
      (∀ x, _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := dimA x) (blocksA x))) →
      (∀ x, _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := dimB x) (blocksB x))) →
      (∀ x, IsIrreducibleTensor (blocksA x)) →
      (∀ x, IsIrreducibleTensor (blocksB x)) →
      (∀ x, 0 < dimA x) →
      (∀ x, 0 < dimB x) →
      Σ DtotA : ℕ, Σ DtotB : ℕ,
        { _hDecomp : ProportionalDecompositionData (d := blockPhysDim d p)
            blocksA blocksB DtotA DtotB //
          StrictAnti (fun x : Fin rA => ‖μA x‖) ∧
          StrictAnti (fun x : Fin rB => ‖μB x‖) ∧
          BlocksNotGaugePhaseEquiv (d := blockPhysDim d p) blocksA ∧
          BlocksNotGaugePhaseEquiv (d := blockPhysDim d p) blocksB ∧
          (∀ x, IsInjective (blocksA x)) ∧
          (∀ x, IsInjective (blocksB x)) }) :
    ∃ p : ℕ, 0 < p ∧
    ∃ P Q : SectorDecomposition (blockPhysDim d p),
      SameMPV₂ P.toTensor Q.toTensor ∧
      HasBNTSectorData P ∧ HasBNTSectorData Q ∧
      SectorBasisOverlapSpanHypotheses P Q := by
  refine sectorBasisOverlapSpanHypotheses_of_reindexedNonzeroParts_bntCover
    A B hSame hReindexed ?_
  intro p zeroTailA zeroTailB rA rB dimA dimB _ _ μA μB blocksA blocksB hp
    hAblocks hBblocks hAPos hBPos hNonzeroPos hZero hμA hμB hTPA hTPB hPrimA hPrimB
    hIrrA hIrrB hDimA hDimB
  obtain ⟨DtotA, DtotB, hPacked⟩ :=
    hRemaining hp hAblocks hBblocks hAPos hBPos hNonzeroPos hZero hμA hμB hTPA hTPB
      hPrimA hPrimB hIrrA hIrrB hDimA hDimB
  rcases hPacked.2 with
    ⟨hAntiA, hAntiB, hNotGpeA, hNotGpeB, hInjA, hInjB⟩
  refine ⟨DtotA, DtotB, ⟨?_⟩⟩
  exact CommonPrimitiveBNTCoverHypotheses.ofCommonPrimitiveData_zeroTailIdentity
    hμA hμB hTPA hTPB hPrimA hPrimB hIrrA hIrrB hAntiA hAntiB hNotGpeA hNotGpeB
    hZero hInjA hInjB hPacked.1

/-- **Sector-basis overlap-span hypotheses from normal-CF-BNT common primitive data,
with the zero-tail identity derived from length-zero proportionality.**

Normal canonical form together with BNT separation for the common primitive
families, proportional-decomposition data, and injectivity of the nonzero blocks
imply the overlap-span hypotheses.  The equality of the zero tails follows from
the length-zero proportionality relation. -/
theorem sectorBasisOverlapSpanHypotheses_of_commonPrimitiveNormalBNTData_zeroTailIdentity
    {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B)
    (hReindexed : CommonSectorRelabelingHypothesis d)
    (hRemaining : ∀ {p zeroTailA zeroTailB rA rB : ℕ}
      {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
      [∀ x : Fin rA, NeZero (dimA x)]
      [∀ x : Fin rB, NeZero (dimB x)]
      {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
      {blocksA : (x : Fin rA) → MPSTensor (blockPhysDim d p) (dimA x)}
      {blocksB : (x : Fin rB) → MPSTensor (blockPhysDim d p) (dimB x)},
      0 < p →
      (∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d p)),
        mpv (blockTensor (d := d) (D := D₁) A p) σ =
          mpv (zeroMPSTensor (blockPhysDim d p) zeroTailA) σ +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) σ) →
      (∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d p)),
        mpv (blockTensor (d := d) (D := D₂) B p) σ =
          mpv (zeroMPSTensor (blockPhysDim d p) zeroTailB) σ +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) σ) →
      SameMPV₂Pos (blockTensor (d := d) (D := D₁) A p)
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) →
      SameMPV₂Pos (blockTensor (d := d) (D := D₂) B p)
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) →
      SameMPV₂Pos
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA)
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) →
      (∀ σ : Fin 0 → Fin (blockPhysDim d p),
        (zeroTailA : ℂ) +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) σ =
          (zeroTailB : ℂ) +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) σ) →
      (∀ x, μA x ≠ 0) →
      (∀ x, μB x ≠ 0) →
      (∀ x, ∑ i : Fin (blockPhysDim d p), (blocksA x i)ᴴ * blocksA x i = 1) →
      (∀ x, ∑ i : Fin (blockPhysDim d p), (blocksB x i)ᴴ * blocksB x i = 1) →
      (∀ x, _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := dimA x) (blocksA x))) →
      (∀ x, _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := dimB x) (blocksB x))) →
      (∀ x, IsIrreducibleTensor (blocksA x)) →
      (∀ x, IsIrreducibleTensor (blocksB x)) →
      (∀ x, 0 < dimA x) →
      (∀ x, 0 < dimB x) →
      Σ DtotA : ℕ, Σ DtotB : ℕ,
        { _hDecomp : ProportionalDecompositionData (d := blockPhysDim d p)
            blocksA blocksB DtotA DtotB //
          IsNormalCanonicalFormBNT (d := blockPhysDim d p) μA blocksA ∧
          IsNormalCanonicalFormBNT (d := blockPhysDim d p) μB blocksB ∧
          (∀ x, IsInjective (blocksA x)) ∧
          (∀ x, IsInjective (blocksB x)) }) :
    ∃ p : ℕ, 0 < p ∧
    ∃ P Q : SectorDecomposition (blockPhysDim d p),
      SameMPV₂ P.toTensor Q.toTensor ∧
      HasBNTSectorData P ∧ HasBNTSectorData Q ∧
      SectorBasisOverlapSpanHypotheses P Q := by
  refine sectorBasisOverlapSpanHypotheses_of_reindexedNonzeroParts_bntCover
    A B hSame hReindexed ?_
  intro p zeroTailA zeroTailB rA rB dimA dimB _ _ μA μB blocksA blocksB hp
    hAblocks hBblocks hAPos hBPos hNonzeroPos hZero hμA hμB hTPA hTPB hPrimA hPrimB
    hIrrA hIrrB hDimA hDimB
  obtain ⟨DtotA, DtotB, hPacked⟩ :=
    hRemaining hp hAblocks hBblocks hAPos hBPos hNonzeroPos hZero hμA hμB hTPA hTPB
      hPrimA hPrimB hIrrA hIrrB hDimA hDimB
  rcases hPacked.2 with ⟨hA, hB, hInjA, hInjB⟩
  refine ⟨DtotA, DtotB, ⟨?_⟩⟩
  exact CommonPrimitiveBNTCoverHypotheses.ofNormalCanonicalFormBNT_zeroTailIdentity
    hA hB hZero hInjA hInjB hPacked.1

/-- **Sector basis overlap-span data via a BNT proportional-decomposition comparison.**

This is the proportional-comparison variant of
`sectorBasisOverlapSpanHypotheses_of_reindexedNonzeroParts`. A BNT proportional-decomposition
conclusion for the two nonzero-weight block families gives a common MPV phase cover, hence the
finite-length span equality needed by the collapsed BNT representative construction. -/
theorem sectorBasisOverlapSpanHypotheses_of_reindexedNonzeroParts_proportional
    {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B)
    (hReindexed : CommonSectorRelabelingHypothesis d)
    (hRemaining : ∀ {p zeroTailA zeroTailB rA rB : ℕ}
      {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
      {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
      {blocksA : (x : Fin rA) → MPSTensor (blockPhysDim d p) (dimA x)}
      {blocksB : (x : Fin rB) → MPSTensor (blockPhysDim d p) (dimB x)},
      0 < p →
      (∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d p)),
        mpv (blockTensor (d := d) (D := D₁) A p) σ =
          mpv (zeroMPSTensor (blockPhysDim d p) zeroTailA) σ +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) σ) →
      (∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d p)),
        mpv (blockTensor (d := d) (D := D₂) B p) σ =
          mpv (zeroMPSTensor (blockPhysDim d p) zeroTailB) σ +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) σ) →
      SameMPV₂Pos (blockTensor (d := d) (D := D₁) A p)
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) →
      SameMPV₂Pos (blockTensor (d := d) (D := D₂) B p)
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) →
      SameMPV₂Pos
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA)
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) →
      (∀ σ : Fin 0 → Fin (blockPhysDim d p),
        (zeroTailA : ℂ) +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) σ =
          (zeroTailB : ℂ) +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) σ) →
      (∀ x, μA x ≠ 0) →
      (∀ x, μB x ≠ 0) →
      (∀ x, ∑ i : Fin (blockPhysDim d p), (blocksA x i)ᴴ * blocksA x i = 1) →
      (∀ x, ∑ i : Fin (blockPhysDim d p), (blocksB x i)ᴴ * blocksB x i = 1) →
      (∀ x, _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := dimA x) (blocksA x))) →
      (∀ x, _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := dimB x) (blocksB x))) →
      (∀ x, IsIrreducibleTensor (blocksA x)) →
      (∀ x, IsIrreducibleTensor (blocksB x)) →
      (∀ x, 0 < dimA x) →
      (∀ x, 0 < dimB x) →
      CommonPrimitiveProportionalHypotheses zeroTailA zeroTailB blocksA blocksB) :
    ∃ p : ℕ, 0 < p ∧
    ∃ P Q : SectorDecomposition (blockPhysDim d p),
      SameMPV₂ P.toTensor Q.toTensor ∧
      HasBNTSectorData P ∧ HasBNTSectorData Q ∧
      SectorBasisOverlapSpanHypotheses P Q := by
  obtain ⟨p, hp, zeroTailA, zeroTailB, rA, dimA, μA, blocksA,
      rB, dimB, μB, blocksB, hAblocks, hBblocks, hAPos, hBPos, hNonzeroPos,
      hZero, hμA, hμB, hTPA, hTPB, hPrimA, hPrimB, hIrrA, hIrrB, hDimA, hDimB⟩ :=
    afterBlocking_commonPrimitiveIrreducibleBlocks_of_reindexedNonzeroParts A B hSame hReindexed
  have hHyp : CommonPrimitiveProportionalHypotheses zeroTailA zeroTailB blocksA blocksB :=
    hRemaining hp hAblocks hBblocks hAPos hBPos hNonzeroPos hZero hμA hμB hTPA hTPB
      hPrimA hPrimB hIrrA hIrrB hDimA hDimB
  have hSpanHyp : CommonPrimitiveSpanHypotheses zeroTailA zeroTailB blocksA blocksB :=
    hHyp.toSpanHypotheses
  letI : ∀ x : Fin rA, NeZero (dimA x) := fun x => ⟨Nat.ne_of_gt (hDimA x)⟩
  letI : ∀ x : Fin rB, NeZero (dimB x) := fun x => ⟨Nat.ne_of_gt (hDimB x)⟩
  let nonzeroA := toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA
  let nonzeroB := toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB
  have hAB : SameMPV₂ (blockTensor (d := d) (D := D₁) A p)
                      (blockTensor (d := d) (D := D₂) B p) :=
    sameMPV₂_blockTensor A B hSame p
  have hNonzero : SameMPV₂ nonzeroA nonzeroB :=
    sameMPV₂_live_of_sameMPV₂_with_zeroTail_eq
      (blockTensor (d := d) (D := D₁) A p)
      (blockTensor (d := d) (D := D₂) B p)
      nonzeroA nonzeroB hAB hAblocks hBblocks hSpanHyp.zeroTail_eq
  obtain ⟨P, Q, hPblocks, hQblocks, hPbnt, hQbnt, hOverlapSpan⟩ :=
    exists_bnt_sectorDecomp_pair_with_overlapSpan_of_block_span_eq
      (d := blockPhysDim d p) μA blocksA μB blocksB hTPA hTPB hIrrA hIrrB
      hPrimA hPrimB hSpanHyp.left_injective hSpanHyp.right_injective hμA hμB hSpanHyp.span_eq
  have hPQeq : SameMPV₂ P.toTensor Q.toTensor := by
    intro N σ
    calc
      mpv P.toTensor σ = mpv nonzeroA σ := hPblocks N σ
      _ = mpv nonzeroB σ := hNonzero N σ
      _ = mpv Q.toTensor σ := (hQblocks N σ).symm
  exact ⟨p, hp, P, Q, hPQeq, hPbnt, hQbnt, hOverlapSpan⟩

end MPSTensor

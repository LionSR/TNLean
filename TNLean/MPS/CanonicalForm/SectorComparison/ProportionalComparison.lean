/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.SectorComparison.BasicSectorComparison

open scoped Matrix BigOperators ComplexOrder MatrixOrder

/-!
# Sector comparisons from common MPV phase covers

The results here give after-blocking sector-comparison consequences from finite-length span
comparisons and common MPV phase covers, and record the special case where the cover comes from a
BNT proportional-decomposition comparison of the nonzero-weight block families.

## Main statements

* `TNLean.MPS.CanonicalForm.SectorComparison.BasicSectorComparison` contains the basic
  block-span sector comparison.
* `afterBlocking_sectorComparison_zeroTail_of_reindexedNonzeroParts_commonPhaseCover` — the
  common-length cyclic-sector output, together with the blocked-word relabeling
  equality and the remaining zero-tail, injectivity, and common-cover assertions,
  implies the sector-weight comparison.
* `afterBlocking_sectorComparison_zeroTail_of_proportionalDecompositionConclusion` —
  the zero-tail common-cover theorem applied to BNT proportional-decomposition data.
* `afterBlocking_sectorComparison_zeroTail_of_reindexedNonzeroParts_spanHypotheses` —
  the common primitive nonzero-sector theorem, followed by the remaining zero-tail,
  injectivity, and finite-length span hypotheses.
* `afterBlocking_commonSector_blockSpan_of_reindexedNonzeroParts` —
  common-length cyclic-sector output with conditional finite-length block-span consequences.
* `afterBlocking_sectorComparison_zeroTail_of_reindexedNonzeroParts_proportional` — the
  same relabeled common-sector output, with the common cover obtained from a BNT
  proportional-decomposition comparison for the produced nonzero-sector families.
* `CommonPrimitiveBNTCoverHypotheses` — bundles the BNT-level remaining hypotheses
  (`IsNormalCanonicalForm`, `BlocksNotGaugePhaseEquiv`, `ProportionalDecompositionData`,
  zero-tail equality, and one-site injectivity) for the common-length cyclic sector families.
  The structure provides `.toMPVCommonPhaseCover` and `.toCommonPrimitivePhaseCoverHypotheses`
  bridges to the common phase-cover layer.
  See the structure docstring for the explicit mathematical gaps that remain.

## References

* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608, Section 2.3 + Appendix A]
* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:2011.12127, Section IV]

## Tags

matrix product states, canonical form, BNT, proportional decomposition
-/

namespace MPSTensor

/-- **Zero-tail sector comparison from common primitive nonzero-sector data.**

The common primitive irreducible block theorem supplies the two nonzero-sector decompositions
obtained after blocked-word reindexing. If the remaining zero-tail equality, one-site
injectivity, and finite-length span equality are supplied for those same families, then the
zero-tail block-span comparison theorem gives the sector-weight conclusion.

This theorem deliberately keeps the blocked-word reindexing equality and the final span or
common-cover assertion as hypotheses, so it does not duplicate the separate coordinate and
common-cover constructions. -/
theorem afterBlocking_sectorComparison_zeroTail_of_reindexedNonzeroParts_spanHypotheses
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
    ∃ p' : ℕ, 0 < p' ∧
    ∃ P Q : SectorDecomposition (blockPhysDim d p'),
      SameMPV₂Pos (blockTensor (d := d) (D := D₁) A p') P.toTensor ∧
      SameMPV₂Pos (blockTensor (d := d) (D := D₂) B p') Q.toTensor ∧
      SameMPV₂ P.toTensor Q.toTensor ∧
      HasBNTSectorData P ∧ HasBNTSectorData Q ∧
      ∃ perm : Fin P.basisCount ≃ Fin Q.basisCount,
      ∃ hCopies : ∀ j, P.copies j = Q.copies (perm j),
      ∃ ζ : Fin P.basisCount → ℂ,
        (∀ j, ζ j ≠ 0) ∧
        ∀ j : Fin P.basisCount,
          Finset.univ.val.map (P.weight j) =
            Finset.univ.val.map
              (fun q => ζ j * Q.weight (perm j) (Fin.cast (hCopies j) q)) := by
  obtain ⟨p, hp, zeroTailA, zeroTailB, rA, dimA, μA, blocksA,
      rB, dimB, μB, blocksB, hAblocks, hBblocks, hAPos, hBPos, hNonzeroPos,
      hZero, hμA, hμB, hTPA, hTPB, hPrimA, hPrimB, hIrrA, hIrrB, hDimA, hDimB⟩ :=
    afterBlocking_commonPrimitiveIrreducibleBlocks_of_reindexedNonzeroParts A B hSame hReindexed
  have hHyp : CommonPrimitiveSpanHypotheses zeroTailA zeroTailB blocksA blocksB :=
    hRemaining hp hAblocks hBblocks hAPos hBPos hNonzeroPos hZero hμA hμB hTPA hTPB
      hPrimA hPrimB hIrrA hIrrB hDimA hDimB
  letI : ∀ x : Fin rA, NeZero (dimA x) := fun x => ⟨Nat.ne_of_gt (hDimA x)⟩
  letI : ∀ x : Fin rB, NeZero (dimB x) := fun x => ⟨Nat.ne_of_gt (hDimB x)⟩
  exact afterBlocking_sectorComparison_zeroTail_of_blockSpan
    A B hSame hp μA blocksA μB blocksB hAblocks hBblocks hHyp.zeroTail_eq hTPA hTPB
    hIrrA hIrrB hPrimA hPrimB hHyp.left_injective hHyp.right_injective
    hμA hμB hHyp.span_eq


/-- **Common-length primitive irreducible sectors with conditional block-span consequences.**

The structural theorem gives the common blocking length and the two primitive irreducible
common-sector nonzero parts, conditional on the equality after relabeling blocked physical words.
This statement records, for exactly those families, that either common MPV phase-cover data or a
BNT proportional-decomposition conclusion supplies the finite-length block-span hypothesis used by
`afterBlocking_sectorComparison_zeroTail_of_blockSpan`.  Thus the remaining mathematical inputs are
kept explicit: the blocked-word relabeling equality, and the later common-phase or BNT matching
comparison. -/
theorem afterBlocking_commonSector_blockSpan_of_reindexedNonzeroParts
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
      (∀ x, 0 < dimB x) ∧
      (MPVCommonPhaseCover blocksA blocksB →
        ∀ N,
          Submodule.span ℂ (Set.range (fun x : Fin rA =>
            mpvState (d := blockPhysDim d p) (blocksA x) N)) =
          Submodule.span ℂ (Set.range (fun y : Fin rB =>
            mpvState (d := blockPhysDim d p) (blocksB y) N))) ∧
      (ProportionalDecompositionConclusion (d := blockPhysDim d p) blocksA blocksB →
        ∀ N,
          Submodule.span ℂ (Set.range (fun x : Fin rA =>
            mpvState (d := blockPhysDim d p) (blocksA x) N)) =
          Submodule.span ℂ (Set.range (fun y : Fin rB =>
            mpvState (d := blockPhysDim d p) (blocksB y) N))) := by
  obtain ⟨p, hp, zeroTailA, zeroTailB, rA, dimA, μA, blocksA,
      rB, dimB, μB, blocksB, hAblocks, hBblocks, hAPos, hBPos, hNonzeroPos,
      hZeroTailIdentity, hμA, hμB, hTPA, hTPB, hPrimA, hPrimB, hIrrA, hIrrB,
      hDimA, hDimB⟩ :=
    afterBlocking_commonPrimitiveIrreducibleBlocks_of_reindexedNonzeroParts
      A B hSame hReindexed
  refine ⟨p, hp, zeroTailA, zeroTailB, rA, dimA, μA, blocksA,
    rB, dimB, μB, blocksB, hAblocks, hBblocks, hAPos, hBPos, hNonzeroPos,
    hZeroTailIdentity, hμA, hμB, hTPA, hTPB, hPrimA, hPrimB, hIrrA, hIrrB,
    hDimA, hDimB, ?_, ?_⟩
  · intro cover N
    exact cover.span_eq N
  · intro hMatch N
    exact mpv_span_eq_of_proportionalDecompositionConclusion
      (d := blockPhysDim d p) blocksA blocksB hMatch N

/-- **Sector comparison from relabeled common sectors and a common phase cover.**

Assume the blocked-word relabeling statement for cyclic-sector data.  Then the
structural theorem
`afterBlocking_commonPrimitiveIrreducibleBlocks_of_reindexedNonzeroParts` supplies one
common positive blocking length and trace-preserving, primitive, irreducible
nonzero-sector families on both sides.  If the remaining comparison assertions
for exactly those families are available -- equality of the two zero-tail
dimensions, injectivity at that blocking level, and a common MPV phase cover --
then `CommonPrimitivePhaseCoverHypotheses.toSpanHypotheses` gives the span hypotheses
needed by `afterBlocking_sectorComparison_zeroTail_of_reindexedNonzeroParts_spanHypotheses`.

Thus this theorem isolates the remaining open inputs: the blocked-word relabeling
equality, the zero-tail/injectivity refinements, and the common phase cover (or
equivalently the finite-length span equality supplied by that cover). -/
theorem afterBlocking_sectorComparison_zeroTail_of_reindexedNonzeroParts_commonPhaseCover
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
    ∃ p' : ℕ, 0 < p' ∧
    ∃ P Q : SectorDecomposition (blockPhysDim d p'),
      SameMPV₂Pos (blockTensor (d := d) (D := D₁) A p') P.toTensor ∧
      SameMPV₂Pos (blockTensor (d := d) (D := D₂) B p') Q.toTensor ∧
      SameMPV₂ P.toTensor Q.toTensor ∧
      HasBNTSectorData P ∧ HasBNTSectorData Q ∧
      ∃ perm : Fin P.basisCount ≃ Fin Q.basisCount,
      ∃ hCopies : ∀ j, P.copies j = Q.copies (perm j),
      ∃ ζ : Fin P.basisCount → ℂ,
        (∀ j, ζ j ≠ 0) ∧
        ∀ j : Fin P.basisCount,
          Finset.univ.val.map (P.weight j) =
            Finset.univ.val.map
              (fun q => ζ j * Q.weight (perm j) (Fin.cast (hCopies j) q)) := by
  refine afterBlocking_sectorComparison_zeroTail_of_reindexedNonzeroParts_spanHypotheses
    A B hSame hReindexed ?_
  intro p zeroTailA zeroTailB rA rB dimA dimB μA μB blocksA blocksB hp
    hAblocks hBblocks hAPos hBPos hNonzeroPos hZero hμA hμB hTPA hTPB hPrimA hPrimB
    hIrrA hIrrB hDimA hDimB
  exact (hRemaining hp hAblocks hBblocks hAPos hBPos hNonzeroPos hZero hμA hμB hTPA hTPB
    hPrimA hPrimB hIrrA hIrrB hDimA hDimB).toSpanHypotheses

/-- **Sector comparison from relabeled common sectors and BNT-cover data.**

Assume the blocked-word relabeling statement for cyclic-sector data. The structural
theorem supplies common primitive nonzero-sector families; if those families carry
BNT-cover data, then the conversion to phase-cover hypotheses gives the common
phase-cover hypotheses. The common-phase-cover consumer theorem gives the same
sector-weight comparison
conclusion. -/
theorem afterBlocking_sectorComparison_zeroTail_of_reindexedNonzeroParts_bntCover
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
    ∃ p' : ℕ, 0 < p' ∧
    ∃ P Q : SectorDecomposition (blockPhysDim d p'),
      SameMPV₂Pos (blockTensor (d := d) (D := D₁) A p') P.toTensor ∧
      SameMPV₂Pos (blockTensor (d := d) (D := D₂) B p') Q.toTensor ∧
      SameMPV₂ P.toTensor Q.toTensor ∧
      HasBNTSectorData P ∧ HasBNTSectorData Q ∧
      ∃ perm : Fin P.basisCount ≃ Fin Q.basisCount,
      ∃ hCopies : ∀ j, P.copies j = Q.copies (perm j),
      ∃ ζ : Fin P.basisCount → ℂ,
        (∀ j, ζ j ≠ 0) ∧
        ∀ j : Fin P.basisCount,
          Finset.univ.val.map (P.weight j) =
            Finset.univ.val.map
              (fun q => ζ j * Q.weight (perm j) (Fin.cast (hCopies j) q)) := by
  refine afterBlocking_sectorComparison_zeroTail_of_reindexedNonzeroParts_commonPhaseCover
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

/-- **Sector comparison from normal-CF-BNT common primitive data.**

Assume the blocked-word relabeling statement for cyclic-sector data.  If the common primitive
families supplied by the structural theorem are already in normal canonical form with BNT
separation, and if they also carry proportional-decomposition data and one-site injectivity,
then the zero-tail sector comparison follows.  The zero-tail equality is derived from the
length-zero identity and the proportional comparison. -/
theorem afterBlocking_sectorComparison_zeroTail_of_commonPrimitiveNormalBNTData_zeroTailIdentity
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
    ∃ p' : ℕ, 0 < p' ∧
    ∃ P Q : SectorDecomposition (blockPhysDim d p'),
      SameMPV₂Pos (blockTensor (d := d) (D := D₁) A p') P.toTensor ∧
      SameMPV₂Pos (blockTensor (d := d) (D := D₂) B p') Q.toTensor ∧
      SameMPV₂ P.toTensor Q.toTensor ∧
      HasBNTSectorData P ∧ HasBNTSectorData Q ∧
      ∃ perm : Fin P.basisCount ≃ Fin Q.basisCount,
      ∃ hCopies : ∀ j, P.copies j = Q.copies (perm j),
      ∃ ζ : Fin P.basisCount → ℂ,
        (∀ j, ζ j ≠ 0) ∧
        ∀ j : Fin P.basisCount,
          Finset.univ.val.map (P.weight j) =
            Finset.univ.val.map
              (fun q => ζ j * Q.weight (perm j) (Fin.cast (hCopies j) q)) := by
  refine afterBlocking_sectorComparison_zeroTail_of_reindexedNonzeroParts_bntCover
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

/-- **Sector comparison from relabeled common sectors and proportional-decomposition data.**

Assume the blocked-word relabeling statement for cyclic-sector data.  Then the
structural theorem
`afterBlocking_commonPrimitiveIrreducibleBlocks_of_reindexedNonzeroParts` supplies one
common positive blocking length and trace-preserving, primitive, irreducible
nonzero-sector families on both sides.  If the remaining comparison assertions
for exactly those families are available -- equality of the two zero-tail
dimensions, injectivity at that blocking level, and a BNT proportional-decomposition
comparison -- then `CommonPrimitiveProportionalHypotheses.toPhaseCoverHypotheses` gives
the common MPV phase-cover hypotheses needed by
`afterBlocking_sectorComparison_zeroTail_of_reindexedNonzeroParts_commonPhaseCover`.

Thus this theorem exposes the BNT comparison as a precise conditional input for the
common-sector families, without assuming a finite-length span equality separately. -/
theorem afterBlocking_sectorComparison_zeroTail_of_reindexedNonzeroParts_proportional
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
    ∃ p' : ℕ, 0 < p' ∧
    ∃ P Q : SectorDecomposition (blockPhysDim d p'),
      SameMPV₂Pos (blockTensor (d := d) (D := D₁) A p') P.toTensor ∧
      SameMPV₂Pos (blockTensor (d := d) (D := D₂) B p') Q.toTensor ∧
      SameMPV₂ P.toTensor Q.toTensor ∧
      HasBNTSectorData P ∧ HasBNTSectorData Q ∧
      ∃ perm : Fin P.basisCount ≃ Fin Q.basisCount,
      ∃ hCopies : ∀ j, P.copies j = Q.copies (perm j),
      ∃ ζ : Fin P.basisCount → ℂ,
        (∀ j, ζ j ≠ 0) ∧
        ∀ j : Fin P.basisCount,
          Finset.univ.val.map (P.weight j) =
            Finset.univ.val.map
              (fun q => ζ j * Q.weight (perm j) (Fin.cast (hCopies j) q)) := by
  refine afterBlocking_sectorComparison_zeroTail_of_reindexedNonzeroParts_commonPhaseCover
    A B hSame hReindexed ?_
  intro p zeroTailA zeroTailB rA rB dimA dimB μA μB blocksA blocksB hp
    hAblocks hBblocks hAPos hBPos hNonzeroPos hZero hμA hμB hTPA hTPB hPrimA hPrimB
    hIrrA hIrrB hDimA hDimB
  exact (hRemaining hp hAblocks hBblocks hAPos hBPos hNonzeroPos hZero hμA hμB hTPA hTPB
    hPrimA hPrimB hIrrA hIrrB hDimA hDimB).toPhaseCoverHypotheses

end MPSTensor

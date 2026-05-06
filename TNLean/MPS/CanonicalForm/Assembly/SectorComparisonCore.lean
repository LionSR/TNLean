/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.Assembly.ZeroTailTransport
import TNLean.MPS.CanonicalForm.EqualNormBridge
import TNLean.MPS.Core.BlockingInfrastructure

open scoped Matrix BigOperators ComplexOrder MatrixOrder

/-!
# Conditional sector comparison after blocking

This module contains the conditional sector-comparison consequences used after
structural common-period blocking.  The statements preserve the historical
public declaration names while separating the BNT/overlap-span comparison layer
from the structural-data construction.

When later statements in this route mention zero-tail data, the term denotes
the total bond dimension of the separated all-zero leftover blocks, namely the
dimension gap allowed by `∑ k, D_k ≤ D`.
-/

namespace MPSTensor

section FundamentalTheoremAfterBlocking

/-- **After-blocking sector comparison from primitive overlap-span hypotheses.**

Assume that a common positive blocking period gives sector decompositions for
the two blocked tensors, that both sector decompositions carry BNT data, and
that their bases satisfy the primitive overlap-span hypotheses. These
hypotheses construct the sector-basis matching, and the two-basis sector
comparison theorem then gives the matched sector-weight conclusion.

Thus the matched sector-weight conclusion is derived from primitive overlap-span
data, rather than from an assumed `SectorBasisMatching` or an assumed
permutation with copy-count equalities. -/
theorem fundamentalTheorem_after_blocking_sector_of_bntPair_overlapSpan
    {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B)
    (bntSectorPair :
      ∃ p : ℕ, 0 < p ∧
      ∃ P Q : SectorDecomposition (blockPhysDim d p),
        SameMPV₂ (blockTensor (d := d) (D := D₁) A p) P.toTensor ∧
        SameMPV₂ (blockTensor (d := d) (D := D₂) B p) Q.toTensor ∧
        HasBNTSectorData P ∧ HasBNTSectorData Q ∧
        SectorBasisOverlapSpanHypotheses P Q) :
    ∃ p : ℕ, 0 < p ∧
    ∃ P Q : SectorDecomposition (blockPhysDim d p),
      SameMPV₂ (blockTensor (d := d) (D := D₁) A p) P.toTensor ∧
      SameMPV₂ (blockTensor (d := d) (D := D₂) B p) Q.toTensor ∧
      HasBNTSectorData P ∧ HasBNTSectorData Q ∧
      ∃ perm : Fin P.basisCount ≃ Fin Q.basisCount,
      ∃ hCopies : ∀ j, P.copies j = Q.copies (perm j),
      ∃ ζ : Fin P.basisCount → ℂ,
        (∀ j, ζ j ≠ 0) ∧
        ∀ j : Fin P.basisCount,
          Finset.univ.val.map (P.weight j) =
            Finset.univ.val.map
              (fun q => ζ j * Q.weight (perm j) (Fin.cast (hCopies j) q)) := by
  obtain ⟨p, hp, P, Q, hPeq, hQeq, hPbnt, hQbnt, hOverlapSpan⟩ := bntSectorPair
  have hAB : SameMPV₂ (blockTensor (d := d) (D := D₁) A p)
                      (blockTensor (d := d) (D := D₂) B p) :=
    sameMPV₂_blockTensor A B hSame p
  have hPQeq : SameMPV₂ P.toTensor Q.toTensor := by
    intro N σ
    calc
      mpv P.toTensor σ
          = mpv (blockTensor (d := d) (D := D₁) A p) σ := (hPeq N σ).symm
      _ = mpv (blockTensor (d := d) (D := D₂) B p) σ := hAB N σ
      _ = mpv Q.toTensor σ := hQeq N σ
  obtain ⟨M⟩ := hOverlapSpan.exists_sectorBasisMatching hPQeq
  obtain ⟨ζ, hζne, hMultiset⟩ :=
    fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_sectorMatching M hPbnt hPQeq
  exact ⟨p, hp, P, Q, hPeq, hQeq, hPbnt, hQbnt,
          M.perm, M.copies_eq, ζ, hζne, hMultiset⟩

/-- **Common nonzero-block construction using the one-sided BNT construction.**

Assume a common blocking period `p` has already produced exact nonzero-block
decompositions of `blockTensor A p` and `blockTensor B p` by TP primitive
irreducible blocks with nonzero weights. The theorem applies the collapsed
one-sided BNT construction
`exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks` on both sides, derives the
equality of the two resulting sector tensors from the original `SameMPV₂ A B`,
and then uses primitive overlap-span data for the constructed sector bases to
produce the matched sector-weight conclusion.

The remaining work to reach the fully unconditional theorem is to obtain these exact
common nonzero-block decompositions, and the overlap-span data for their BNT
sector bases, from the current structural reduction without extra hypotheses. -/
theorem fundamentalTheorem_after_blocking_sector_of_common_blocks_overlapSpan
    {d D₁ D₂ p rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k : Fin rA, NeZero (dimA k)]
    [∀ k : Fin rB, NeZero (dimB k)]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B)
    (hp : 0 < p)
    (μA : Fin rA → ℂ)
    (blocksA : (k : Fin rA) → MPSTensor (blockPhysDim d p) (dimA k))
    (μB : Fin rB → ℂ)
    (blocksB : (k : Fin rB) → MPSTensor (blockPhysDim d p) (dimB k))
    (hAblocks : SameMPV₂ (blockTensor (d := d) (D := D₁) A p)
      (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA))
    (hBblocks : SameMPV₂ (blockTensor (d := d) (D := D₂) B p)
      (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB))
    (hTPA : ∀ k, ∑ i : Fin (blockPhysDim d p), (blocksA k i)ᴴ * blocksA k i = 1)
    (hTPB : ∀ k, ∑ i : Fin (blockPhysDim d p), (blocksB k i)ᴴ * blocksB k i = 1)
    (hIrrA : ∀ k, IsIrreducibleTensor (blocksA k))
    (hIrrB : ∀ k, IsIrreducibleTensor (blocksB k))
    (hPrimA : ∀ k, _root_.IsPrimitive
      (transferMap (d := blockPhysDim d p) (D := dimA k) (blocksA k)))
    (hPrimB : ∀ k, _root_.IsPrimitive
      (transferMap (d := blockPhysDim d p) (D := dimB k) (blocksB k)))
    (hμA : ∀ k, μA k ≠ 0)
    (hμB : ∀ k, μB k ≠ 0)
    (overlapSpanData :
      ∀ P Q : SectorDecomposition (blockPhysDim d p),
        SameMPV₂ P.toTensor (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) →
        SameMPV₂ Q.toTensor (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) →
        HasBNTSectorData P → HasBNTSectorData Q →
        SectorBasisOverlapSpanHypotheses P Q) :
    ∃ p' : ℕ, 0 < p' ∧
    ∃ P Q : SectorDecomposition (blockPhysDim d p'),
      SameMPV₂ (blockTensor (d := d) (D := D₁) A p') P.toTensor ∧
      SameMPV₂ (blockTensor (d := d) (D := D₂) B p') Q.toTensor ∧
      HasBNTSectorData P ∧ HasBNTSectorData Q ∧
      ∃ perm : Fin P.basisCount ≃ Fin Q.basisCount,
      ∃ hCopies : ∀ j, P.copies j = Q.copies (perm j),
      ∃ ζ : Fin P.basisCount → ℂ,
        (∀ j, ζ j ≠ 0) ∧
        ∀ j : Fin P.basisCount,
          Finset.univ.val.map (P.weight j) =
            Finset.univ.val.map
              (fun q => ζ j * Q.weight (perm j) (Fin.cast (hCopies j) q)) := by
  obtain ⟨P, hPblocks, hPbnt⟩ :=
    exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks
      (d := blockPhysDim d p) μA blocksA hTPA hIrrA hPrimA hμA
  obtain ⟨Q, hQblocks, hQbnt⟩ :=
    exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks
      (d := blockPhysDim d p) μB blocksB hTPB hIrrB hPrimB hμB
  have hPeq : SameMPV₂ (blockTensor (d := d) (D := D₁) A p) P.toTensor := by
    intro N σ
    calc
      mpv (blockTensor (d := d) (D := D₁) A p) σ
          = mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) σ :=
            hAblocks N σ
      _ = mpv P.toTensor σ := (hPblocks N σ).symm
  have hQeq : SameMPV₂ (blockTensor (d := d) (D := D₂) B p) Q.toTensor := by
    intro N σ
    calc
      mpv (blockTensor (d := d) (D := D₂) B p) σ
          = mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) σ :=
            hBblocks N σ
      _ = mpv Q.toTensor σ := (hQblocks N σ).symm
  have hAB : SameMPV₂ (blockTensor (d := d) (D := D₁) A p)
                      (blockTensor (d := d) (D := D₂) B p) :=
    sameMPV₂_blockTensor A B hSame p
  have hPQeq : SameMPV₂ P.toTensor Q.toTensor := by
    intro N σ
    calc
      mpv P.toTensor σ
          = mpv (blockTensor (d := d) (D := D₁) A p) σ := (hPeq N σ).symm
      _ = mpv (blockTensor (d := d) (D := D₂) B p) σ := hAB N σ
      _ = mpv Q.toTensor σ := hQeq N σ
  have hOverlapSpan := overlapSpanData P Q hPblocks hQblocks hPbnt hQbnt
  obtain ⟨M⟩ := hOverlapSpan.exists_sectorBasisMatching hPQeq
  obtain ⟨ζ, hζne, hMultiset⟩ :=
    fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_sectorMatching M hPbnt hPQeq
  exact ⟨p, hp, P, Q, hPeq, hQeq, hPbnt, hQbnt,
          M.perm, M.copies_eq, ζ, hζne, hMultiset⟩

/-- **Common nonzero-block sector comparison with an explicit zero-tail identity.**

This is the zero-tail-aware variant of
`fundamentalTheorem_after_blocking_sector_of_common_blocks_overlapSpan`.
The blocked tensors are related to their nonzero parts only at positive lengths,
which is the strongest statement available after removing a nonzero zero tail. If the two
zero-tail dimensions agree, the nonzero parts themselves are full `SameMPV₂`, including `N = 0`,
so the existing sector-matching layer applies unchanged. -/
theorem fundamentalTheorem_after_blocking_sector_of_common_blocks_overlapSpan_zeroTail
    {d D₁ D₂ p rA rB zeroTailA zeroTailB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k : Fin rA, NeZero (dimA k)]
    [∀ k : Fin rB, NeZero (dimB k)]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B)
    (hp : 0 < p)
    (μA : Fin rA → ℂ)
    (blocksA : (k : Fin rA) → MPSTensor (blockPhysDim d p) (dimA k))
    (μB : Fin rB → ℂ)
    (blocksB : (k : Fin rB) → MPSTensor (blockPhysDim d p) (dimB k))
    (hAblocks :
      ∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d p)),
        mpv (blockTensor (d := d) (D := D₁) A p) σ =
          mpv (zeroMPSTensor (blockPhysDim d p) zeroTailA) σ +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) σ)
    (hBblocks :
      ∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d p)),
        mpv (blockTensor (d := d) (D := D₂) B p) σ =
          mpv (zeroMPSTensor (blockPhysDim d p) zeroTailB) σ +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) σ)
    (hZeroTail : zeroTailA = zeroTailB)
    (hTPA : ∀ k, ∑ i : Fin (blockPhysDim d p), (blocksA k i)ᴴ * blocksA k i = 1)
    (hTPB : ∀ k, ∑ i : Fin (blockPhysDim d p), (blocksB k i)ᴴ * blocksB k i = 1)
    (hIrrA : ∀ k, IsIrreducibleTensor (blocksA k))
    (hIrrB : ∀ k, IsIrreducibleTensor (blocksB k))
    (hPrimA : ∀ k, _root_.IsPrimitive
      (transferMap (d := blockPhysDim d p) (D := dimA k) (blocksA k)))
    (hPrimB : ∀ k, _root_.IsPrimitive
      (transferMap (d := blockPhysDim d p) (D := dimB k) (blocksB k)))
    (hμA : ∀ k, μA k ≠ 0)
    (hμB : ∀ k, μB k ≠ 0)
    (overlapSpanData :
      ∀ P Q : SectorDecomposition (blockPhysDim d p),
        SameMPV₂ P.toTensor (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) →
        SameMPV₂ Q.toTensor (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) →
        HasBNTSectorData P → HasBNTSectorData Q →
        SectorBasisOverlapSpanHypotheses P Q) :
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
  let liveA := toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA
  let liveB := toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB
  obtain ⟨P, hPblocks, hPbnt⟩ :=
    exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks
      (d := blockPhysDim d p) μA blocksA hTPA hIrrA hPrimA hμA
  obtain ⟨Q, hQblocks, hQbnt⟩ :=
    exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks
      (d := blockPhysDim d p) μB blocksB hTPB hIrrB hPrimB hμB
  have hAB : SameMPV₂ (blockTensor (d := d) (D := D₁) A p)
                      (blockTensor (d := d) (D := D₂) B p) :=
    sameMPV₂_blockTensor A B hSame p
  have hLive : SameMPV₂ liveA liveB :=
    sameMPV₂_live_of_sameMPV₂_with_zeroTail_eq
      (blockTensor (d := d) (D := D₁) A p)
      (blockTensor (d := d) (D := D₂) B p)
      liveA liveB hAB hAblocks hBblocks hZeroTail
  have hPeqPos : SameMPV₂Pos (blockTensor (d := d) (D := D₁) A p) P.toTensor := by
    intro N hN σ
    have hZero :
        mpv (zeroMPSTensor (blockPhysDim d p) zeroTailA) σ = 0 := by
      rw [mpv_zeroMPSTensor]
      simp [Nat.ne_of_gt hN]
    calc
      mpv (blockTensor (d := d) (D := D₁) A p) σ
          = mpv (zeroMPSTensor (blockPhysDim d p) zeroTailA) σ + mpv liveA σ :=
            hAblocks N σ
      _ = mpv liveA σ := by rw [hZero]; simp
      _ = mpv P.toTensor σ := (hPblocks N σ).symm
  have hQeqPos : SameMPV₂Pos (blockTensor (d := d) (D := D₂) B p) Q.toTensor := by
    intro N hN σ
    have hZero :
        mpv (zeroMPSTensor (blockPhysDim d p) zeroTailB) σ = 0 := by
      rw [mpv_zeroMPSTensor]
      simp [Nat.ne_of_gt hN]
    calc
      mpv (blockTensor (d := d) (D := D₂) B p) σ
          = mpv (zeroMPSTensor (blockPhysDim d p) zeroTailB) σ + mpv liveB σ :=
            hBblocks N σ
      _ = mpv liveB σ := by rw [hZero]; simp
      _ = mpv Q.toTensor σ := (hQblocks N σ).symm
  have hPQeq : SameMPV₂ P.toTensor Q.toTensor := by
    intro N σ
    calc
      mpv P.toTensor σ = mpv liveA σ := hPblocks N σ
      _ = mpv liveB σ := hLive N σ
      _ = mpv Q.toTensor σ := (hQblocks N σ).symm
  have hOverlapSpan := overlapSpanData P Q hPblocks hQblocks hPbnt hQbnt
  obtain ⟨M⟩ := hOverlapSpan.exists_sectorBasisMatching hPQeq
  obtain ⟨ζ, hζne, hMultiset⟩ :=
    fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_sectorMatching M hPbnt hPQeq
  exact ⟨p, hp, P, Q, hPeqPos, hQeqPos, hPQeq, hPbnt, hQbnt,
          M.perm, M.copies_eq, ζ, hζne, hMultiset⟩

/-- **Common nonzero-block construction with derived one-sided overlap data.**

This nonzero-part variant of
`fundamentalTheorem_after_blocking_sector_of_common_blocks_overlapSpan`
uses the phase-class BNT construction to derive the positive-dimension,
normalization, self-overlap, and off-overlap hypotheses, and to transfer the supplied
one-site injectivity of the nonzero-weight blocks to the chosen basis blocks. The remaining
two-basis analytic hypothesis is the finite-length span comparison between the two
constructed bases. -/
theorem fundamentalTheorem_after_blocking_sector_of_common_blocks_injectiveSpan
    {d D₁ D₂ p rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k : Fin rA, NeZero (dimA k)]
    [∀ k : Fin rB, NeZero (dimB k)]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B)
    (hp : 0 < p)
    (μA : Fin rA → ℂ)
    (blocksA : (k : Fin rA) → MPSTensor (blockPhysDim d p) (dimA k))
    (μB : Fin rB → ℂ)
    (blocksB : (k : Fin rB) → MPSTensor (blockPhysDim d p) (dimB k))
    (hAblocks : SameMPV₂ (blockTensor (d := d) (D := D₁) A p)
      (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA))
    (hBblocks : SameMPV₂ (blockTensor (d := d) (D := D₂) B p)
      (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB))
    (hTPA : ∀ k, ∑ i : Fin (blockPhysDim d p), (blocksA k i)ᴴ * blocksA k i = 1)
    (hTPB : ∀ k, ∑ i : Fin (blockPhysDim d p), (blocksB k i)ᴴ * blocksB k i = 1)
    (hIrrA : ∀ k, IsIrreducibleTensor (blocksA k))
    (hIrrB : ∀ k, IsIrreducibleTensor (blocksB k))
    (hPrimA : ∀ k, _root_.IsPrimitive
      (transferMap (d := blockPhysDim d p) (D := dimA k) (blocksA k)))
    (hPrimB : ∀ k, _root_.IsPrimitive
      (transferMap (d := blockPhysDim d p) (D := dimB k) (blocksB k)))
    (hInjA : ∀ k, IsInjective (blocksA k))
    (hInjB : ∀ k, IsInjective (blocksB k))
    (hμA : ∀ k, μA k ≠ 0)
    (hμB : ∀ k, μB k ≠ 0)
    (spanData :
      ∀ P Q : SectorDecomposition (blockPhysDim d p),
        SameMPV₂ P.toTensor (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) →
        SameMPV₂ Q.toTensor (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) →
        HasBNTSectorData P → HasBNTSectorData Q →
        SectorBasisOverlapOrthoHypotheses P → SectorBasisOverlapOrthoHypotheses Q →
        ∀ N,
          Submodule.span ℂ (Set.range (fun j : Fin P.basisCount =>
            mpvState (d := blockPhysDim d p) (P.basis j) N)) =
          Submodule.span ℂ (Set.range (fun k : Fin Q.basisCount =>
            mpvState (d := blockPhysDim d p) (Q.basis k) N))) :
    ∃ p' : ℕ, 0 < p' ∧
    ∃ P Q : SectorDecomposition (blockPhysDim d p'),
      SameMPV₂ (blockTensor (d := d) (D := D₁) A p') P.toTensor ∧
      SameMPV₂ (blockTensor (d := d) (D := D₂) B p') Q.toTensor ∧
      HasBNTSectorData P ∧ HasBNTSectorData Q ∧
      ∃ perm : Fin P.basisCount ≃ Fin Q.basisCount,
      ∃ hCopies : ∀ j, P.copies j = Q.copies (perm j),
      ∃ ζ : Fin P.basisCount → ℂ,
        (∀ j, ζ j ≠ 0) ∧
        ∀ j : Fin P.basisCount,
          Finset.univ.val.map (P.weight j) =
            Finset.univ.val.map
              (fun q => ζ j * Q.weight (perm j) (Fin.cast (hCopies j) q)) := by
  obtain ⟨P, hPblocks, hPbnt, hPOrtho, hPInj_of⟩ :=
    exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks_with_overlapOrtho
      (d := blockPhysDim d p) μA blocksA hTPA hIrrA hPrimA hμA
  obtain ⟨Q, hQblocks, hQbnt, hQOrtho, hQInj_of⟩ :=
    exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks_with_overlapOrtho
      (d := blockPhysDim d p) μB blocksB hTPB hIrrB hPrimB hμB
  have hPeq : SameMPV₂ (blockTensor (d := d) (D := D₁) A p) P.toTensor := by
    intro N σ
    calc
      mpv (blockTensor (d := d) (D := D₁) A p) σ
          = mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) σ :=
            hAblocks N σ
      _ = mpv P.toTensor σ := (hPblocks N σ).symm
  have hQeq : SameMPV₂ (blockTensor (d := d) (D := D₂) B p) Q.toTensor := by
    intro N σ
    calc
      mpv (blockTensor (d := d) (D := D₂) B p) σ
          = mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) σ :=
            hBblocks N σ
      _ = mpv Q.toTensor σ := (hQblocks N σ).symm
  have hAB : SameMPV₂ (blockTensor (d := d) (D := D₁) A p)
                      (blockTensor (d := d) (D := D₂) B p) :=
    sameMPV₂_blockTensor A B hSame p
  have hPQeq : SameMPV₂ P.toTensor Q.toTensor := by
    intro N σ
    calc
      mpv P.toTensor σ
          = mpv (blockTensor (d := d) (D := D₁) A p) σ := (hPeq N σ).symm
      _ = mpv (blockTensor (d := d) (D := D₂) B p) σ := hAB N σ
      _ = mpv Q.toTensor σ := hQeq N σ
  have hSpan := spanData P Q hPblocks hQblocks hPbnt hQbnt hPOrtho hQOrtho
  have hOverlapSpan : SectorBasisOverlapSpanHypotheses P Q :=
    hPOrtho.to_overlapSpan hQOrtho (hPInj_of hInjA) (hQInj_of hInjB) hSpan
  obtain ⟨M⟩ := hOverlapSpan.exists_sectorBasisMatching hPQeq
  obtain ⟨ζ, hζne, hMultiset⟩ :=
    fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_sectorMatching M hPbnt hPQeq
  exact ⟨p, hp, P, Q, hPeq, hQeq, hPbnt, hQbnt,
          M.perm, M.copies_eq, ζ, hζne, hMultiset⟩

/-- **Common nonzero-block construction from nonzero-block span equality.**

This nonzero-part variant replaces the opaque two-sector `overlapSpanData` hypothesis in
`fundamentalTheorem_after_blocking_sector_of_common_blocks_overlapSpan`. The
one-sided MPV phase-equivalence class representative construction supplies positive
dimensions, injectivity, normalization, and the asymptotic overlap data for the
representative bases. The remaining two-family analytic hypothesis is the finite-length span
equality for the original nonzero-weight block families;
`exists_bnt_sectorDecomp_pair_with_overlapSpan_of_block_span_eq` transports it to the chosen
sector bases. -/
theorem fundamentalTheorem_after_blocking_sector_of_common_blocks_blockSpan
    {d D₁ D₂ p rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k : Fin rA, NeZero (dimA k)]
    [∀ k : Fin rB, NeZero (dimB k)]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B)
    (hp : 0 < p)
    (μA : Fin rA → ℂ)
    (blocksA : (k : Fin rA) → MPSTensor (blockPhysDim d p) (dimA k))
    (μB : Fin rB → ℂ)
    (blocksB : (k : Fin rB) → MPSTensor (blockPhysDim d p) (dimB k))
    (hAblocks : SameMPV₂ (blockTensor (d := d) (D := D₁) A p)
      (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA))
    (hBblocks : SameMPV₂ (blockTensor (d := d) (D := D₂) B p)
      (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB))
    (hTPA : ∀ k, ∑ i : Fin (blockPhysDim d p), (blocksA k i)ᴴ * blocksA k i = 1)
    (hTPB : ∀ k, ∑ i : Fin (blockPhysDim d p), (blocksB k i)ᴴ * blocksB k i = 1)
    (hIrrA : ∀ k, IsIrreducibleTensor (blocksA k))
    (hIrrB : ∀ k, IsIrreducibleTensor (blocksB k))
    (hPrimA : ∀ k, _root_.IsPrimitive
      (transferMap (d := blockPhysDim d p) (D := dimA k) (blocksA k)))
    (hPrimB : ∀ k, _root_.IsPrimitive
      (transferMap (d := blockPhysDim d p) (D := dimB k) (blocksB k)))
    (hInjA : ∀ k, IsInjective (blocksA k))
    (hInjB : ∀ k, IsInjective (blocksB k))
    (hμA : ∀ k, μA k ≠ 0)
    (hμB : ∀ k, μB k ≠ 0)
    (hBlockSpan : ∀ N,
      Submodule.span ℂ (Set.range (fun k : Fin rA =>
        mpvState (d := blockPhysDim d p) (blocksA k) N)) =
      Submodule.span ℂ (Set.range (fun k : Fin rB =>
        mpvState (d := blockPhysDim d p) (blocksB k) N))) :
    ∃ p' : ℕ, 0 < p' ∧
    ∃ P Q : SectorDecomposition (blockPhysDim d p'),
      SameMPV₂ (blockTensor (d := d) (D := D₁) A p') P.toTensor ∧
      SameMPV₂ (blockTensor (d := d) (D := D₂) B p') Q.toTensor ∧
      HasBNTSectorData P ∧ HasBNTSectorData Q ∧
      ∃ perm : Fin P.basisCount ≃ Fin Q.basisCount,
      ∃ hCopies : ∀ j, P.copies j = Q.copies (perm j),
      ∃ ζ : Fin P.basisCount → ℂ,
        (∀ j, ζ j ≠ 0) ∧
        ∀ j : Fin P.basisCount,
          Finset.univ.val.map (P.weight j) =
            Finset.univ.val.map
              (fun q => ζ j * Q.weight (perm j) (Fin.cast (hCopies j) q)) := by
  obtain ⟨P, Q, hPblocks, hQblocks, hPbnt, hQbnt, hOverlapSpan⟩ :=
    exists_bnt_sectorDecomp_pair_with_overlapSpan_of_block_span_eq
      (d := blockPhysDim d p) μA blocksA μB blocksB hTPA hTPB hIrrA hIrrB
      hPrimA hPrimB hInjA hInjB hμA hμB hBlockSpan
  have hPeq : SameMPV₂ (blockTensor (d := d) (D := D₁) A p) P.toTensor := by
    intro N σ
    calc
      mpv (blockTensor (d := d) (D := D₁) A p) σ
          = mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) σ :=
            hAblocks N σ
      _ = mpv P.toTensor σ := (hPblocks N σ).symm
  have hQeq : SameMPV₂ (blockTensor (d := d) (D := D₂) B p) Q.toTensor := by
    intro N σ
    calc
      mpv (blockTensor (d := d) (D := D₂) B p) σ
          = mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) σ :=
            hBblocks N σ
      _ = mpv Q.toTensor σ := (hQblocks N σ).symm
  have hAB : SameMPV₂ (blockTensor (d := d) (D := D₁) A p)
                      (blockTensor (d := d) (D := D₂) B p) :=
    sameMPV₂_blockTensor A B hSame p
  have hPQeq : SameMPV₂ P.toTensor Q.toTensor := by
    intro N σ
    calc
      mpv P.toTensor σ
          = mpv (blockTensor (d := d) (D := D₁) A p) σ := (hPeq N σ).symm
      _ = mpv (blockTensor (d := d) (D := D₂) B p) σ := hAB N σ
      _ = mpv Q.toTensor σ := hQeq N σ
  obtain ⟨M⟩ := hOverlapSpan.exists_sectorBasisMatching hPQeq
  obtain ⟨ζ, hζne, hMultiset⟩ :=
    fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_sectorMatching M hPbnt hPQeq
  exact ⟨p, hp, P, Q, hPeq, hQeq, hPbnt, hQbnt,
          M.perm, M.copies_eq, ζ, hζne, hMultiset⟩

/-- **Common nonzero-block construction from a common MPV-phase cover.**

This nonzero-part variant proves the nonzero-block span equality required by
`fundamentalTheorem_after_blocking_sector_of_common_blocks_blockSpan` from a stronger
common-structure hypothesis: both nonzero-weight block families map onto one common family
of MPV phase classes, and every block is MPV-phase equivalent to its image.  The conclusion
is the same sector-weight comparison as the block-span theorem.

This theorem is a paper-faithful predecessor whose conclusion follows once the common family and
the two surjective class maps are available (via `mpv_span_eq_of_common_phase_cover`). -/
theorem fundamentalTheorem_after_blocking_sector_of_common_blocks_phaseCover
    {d D₁ D₂ p rA rB rC : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ} {dimC : Fin rC → ℕ}
    [∀ k : Fin rA, NeZero (dimA k)]
    [∀ k : Fin rB, NeZero (dimB k)]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B)
    (hp : 0 < p)
    (μA : Fin rA → ℂ)
    (blocksA : (k : Fin rA) → MPSTensor (blockPhysDim d p) (dimA k))
    (μB : Fin rB → ℂ)
    (blocksB : (k : Fin rB) → MPSTensor (blockPhysDim d p) (dimB k))
    (common : (c : Fin rC) → MPSTensor (blockPhysDim d p) (dimC c))
    (classA : Fin rA → Fin rC) (classB : Fin rB → Fin rC)
    (hAphase : ∀ k : Fin rA, MPVBlockPhaseEquiv (common (classA k)) (blocksA k))
    (hBphase : ∀ k : Fin rB, MPVBlockPhaseEquiv (common (classB k)) (blocksB k))
    (hAsurj : Function.Surjective classA)
    (hBsurj : Function.Surjective classB)
    (hAblocks : SameMPV₂ (blockTensor (d := d) (D := D₁) A p)
      (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA))
    (hBblocks : SameMPV₂ (blockTensor (d := d) (D := D₂) B p)
      (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB))
    (hTPA : ∀ k, ∑ i : Fin (blockPhysDim d p), (blocksA k i)ᴴ * blocksA k i = 1)
    (hTPB : ∀ k, ∑ i : Fin (blockPhysDim d p), (blocksB k i)ᴴ * blocksB k i = 1)
    (hIrrA : ∀ k, IsIrreducibleTensor (blocksA k))
    (hIrrB : ∀ k, IsIrreducibleTensor (blocksB k))
    (hPrimA : ∀ k, _root_.IsPrimitive
      (transferMap (d := blockPhysDim d p) (D := dimA k) (blocksA k)))
    (hPrimB : ∀ k, _root_.IsPrimitive
      (transferMap (d := blockPhysDim d p) (D := dimB k) (blocksB k)))
    (hInjA : ∀ k, IsInjective (blocksA k))
    (hInjB : ∀ k, IsInjective (blocksB k))
    (hμA : ∀ k, μA k ≠ 0)
    (hμB : ∀ k, μB k ≠ 0) :
    ∃ p' : ℕ, 0 < p' ∧
    ∃ P Q : SectorDecomposition (blockPhysDim d p'),
      SameMPV₂ (blockTensor (d := d) (D := D₁) A p') P.toTensor ∧
      SameMPV₂ (blockTensor (d := d) (D := D₂) B p') Q.toTensor ∧
      HasBNTSectorData P ∧ HasBNTSectorData Q ∧
      ∃ perm : Fin P.basisCount ≃ Fin Q.basisCount,
      ∃ hCopies : ∀ j, P.copies j = Q.copies (perm j),
      ∃ ζ : Fin P.basisCount → ℂ,
        (∀ j, ζ j ≠ 0) ∧
        ∀ j : Fin P.basisCount,
          Finset.univ.val.map (P.weight j) =
            Finset.univ.val.map
              (fun q => ζ j * Q.weight (perm j) (Fin.cast (hCopies j) q)) := by
  refine fundamentalTheorem_after_blocking_sector_of_common_blocks_blockSpan
    A B hSame hp μA blocksA μB blocksB hAblocks hBblocks hTPA hTPB hIrrA hIrrB
    hPrimA hPrimB hInjA hInjB hμA hμB ?_
  intro N
  exact mpv_span_eq_of_common_phase_cover (d := blockPhysDim d p)
    blocksA blocksB common classA classB hAphase hBphase hAsurj hBsurj N

/-- **Common nonzero-block sector comparison from common MPV-phase-cover data.**

This is the common-cover form of
`fundamentalTheorem_after_blocking_sector_of_common_blocks_phaseCover`: the
common family, the two class maps, the MPV-phase identifications, and the
surjectivity proofs are supplied by `MPVCommonPhaseCover`.  It does not
construct that cover from the structural `SameMPV₂` hypothesis; that cross-side
BNT comparison is a remaining paper-level hypothesis. -/
theorem fundamentalTheorem_after_blocking_sector_of_common_blocks_commonPhaseCover
    {d D₁ D₂ p rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k : Fin rA, NeZero (dimA k)]
    [∀ k : Fin rB, NeZero (dimB k)]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B)
    (hp : 0 < p)
    (μA : Fin rA → ℂ)
    (blocksA : (k : Fin rA) → MPSTensor (blockPhysDim d p) (dimA k))
    (μB : Fin rB → ℂ)
    (blocksB : (k : Fin rB) → MPSTensor (blockPhysDim d p) (dimB k))
    (cover : MPVCommonPhaseCover blocksA blocksB)
    (hAblocks : SameMPV₂ (blockTensor (d := d) (D := D₁) A p)
      (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA))
    (hBblocks : SameMPV₂ (blockTensor (d := d) (D := D₂) B p)
      (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB))
    (hTPA : ∀ k, ∑ i : Fin (blockPhysDim d p), (blocksA k i)ᴴ * blocksA k i = 1)
    (hTPB : ∀ k, ∑ i : Fin (blockPhysDim d p), (blocksB k i)ᴴ * blocksB k i = 1)
    (hIrrA : ∀ k, IsIrreducibleTensor (blocksA k))
    (hIrrB : ∀ k, IsIrreducibleTensor (blocksB k))
    (hPrimA : ∀ k, _root_.IsPrimitive
      (transferMap (d := blockPhysDim d p) (D := dimA k) (blocksA k)))
    (hPrimB : ∀ k, _root_.IsPrimitive
      (transferMap (d := blockPhysDim d p) (D := dimB k) (blocksB k)))
    (hInjA : ∀ k, IsInjective (blocksA k))
    (hInjB : ∀ k, IsInjective (blocksB k))
    (hμA : ∀ k, μA k ≠ 0)
    (hμB : ∀ k, μB k ≠ 0) :
    ∃ p' : ℕ, 0 < p' ∧
    ∃ P Q : SectorDecomposition (blockPhysDim d p'),
      SameMPV₂ (blockTensor (d := d) (D := D₁) A p') P.toTensor ∧
      SameMPV₂ (blockTensor (d := d) (D := D₂) B p') Q.toTensor ∧
      HasBNTSectorData P ∧ HasBNTSectorData Q ∧
      ∃ perm : Fin P.basisCount ≃ Fin Q.basisCount,
      ∃ hCopies : ∀ j, P.copies j = Q.copies (perm j),
      ∃ ζ : Fin P.basisCount → ℂ,
        (∀ j, ζ j ≠ 0) ∧
        ∀ j : Fin P.basisCount,
          Finset.univ.val.map (P.weight j) =
            Finset.univ.val.map
              (fun q => ζ j * Q.weight (perm j) (Fin.cast (hCopies j) q)) :=
  fundamentalTheorem_after_blocking_sector_of_common_blocks_phaseCover
    A B hSame hp μA blocksA μB blocksB cover.common cover.classA cover.classB
    cover.phaseA cover.phaseB cover.surjA cover.surjB hAblocks hBblocks
    hTPA hTPB hIrrA hIrrB hPrimA hPrimB hInjA hInjB hμA hμB


end FundamentalTheoremAfterBlocking

end MPSTensor

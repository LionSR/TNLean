/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.Assembly.CyclicSectorDecomposition
import TNLean.MPS.CanonicalForm.EqualNormBridge

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Filter

/-!
# Structural after-blocking theorem for canonical-form reduction

This file collects the final structural statements in the current
arXiv:1606.00608 reduction chain. It gives a common-period blocking theorem
for two tensors and the resulting structural after-blocking statement that both
sides have TP-primitive decompositions.

## Main statements

* `bilateral_commonPeriod_blocking_tp_primitive_normal` — two tensors with
  primitive blocked transfer maps have a common positive blocking period that
  preserves primitivity, left-canonical normalization, and normality.
* `fundamentalTheorem_after_blocking_1606_structural` — two tensors with the
  same MPVs have blocked TP-primitive decompositions on both sides.

## References

* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608, §2.3 + Appendix A]
* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:2011.12127, §IV]

## Tags

matrix product states, canonical form, common period, fundamental theorem
-/

namespace MPSTensor

variable {d D : ℕ}

/-!
## Fundamental Theorem of MPS (arXiv:1606.00608, after blocking)

### Overview

The fundamental theorem of MPS (1606.00608 version, after blocking) asserts:

For any MPS tensor `A`, there exists a blocking period `p > 0` such that
`blockTensor A p` has a decomposition into a trivial block plus a direct sum
of TP sectors, where each sector is left-canonical and the direct sum is
`SameMPV₂`-equivalent to the blocked tensor.

The full end-to-end statement chains:
1. Zero-block separation (`exists_irreducible_blockDecomp_liveBlocks`)
2. TP gauge (`exists_tp_gauge_from_arbitrary_with_zeroTail`)
3. Common blocking to primitive (`exists_common_blocking_all_primitive_of_TP_irr`)
4. Cyclic sector decomposition per block (`exists_cyclic_sector_decomp_after_blocking`)

### Current status

The theorem `exists_tp_sector_decomp_after_blocking` below provides:
- A blocking period `p > 0`
- A trivial block of dimension `zeroTailDim`
- A family of TP sector blocks
- The MPV relationship: `blockTensor A p` is `SameMPV₂`-equivalent to
  `zeroMPSTensor + toTensorFromBlocks μ sectors` for some weights `μ`

The current library already settles the common-period blocking arithmetic and
now has both a one-sided collapsed BNT construction for TP primitive irreducible
live blocks and a witness-producing sector comparison from primitive
overlap-span hypotheses.  The strongest assembled theorem in this file,
`fundamentalTheorem_after_blocking_1606_sector_of_common_blocks_overlapSpan`,
threads `SameMPV₂ A B` through those ingredients once exact common live block
decompositions and the overlap-span hypotheses are supplied.

The remaining Gap §1 content is to derive those exact live decompositions and the
primitive overlap-span hypotheses from the structural after-blocking reduction
itself, including the zero-tail bookkeeping at length `N = 0`.
-/

section FundamentalTheorem1606

-- **Structural decomposition of MPS tensors after blocking (1606.00608 reduction).**
--
-- For any MPS tensor `A`, there exists a blocking period `p > 0` and a
-- decomposition of the blocked tensor into:
-- 1. A trivial block (irreducible blocks with zero spectral weight)
-- 2. A family of TP blocks with primitive transfer maps
--
-- Additionally, the weights `μ k` satisfy `μ k ≠ 0` and the full MPV
-- identity is maintained.
--
-- This is `exists_tp_primitive_blockDecomp_after_blocking` — the main reduction
-- theorem from the first section. The FT chains from this through the cyclic
-- sector decomposition to produce the final canonical form.
-- (Already proved above as `exists_tp_primitive_blockDecomp_after_blocking`.)

/-- **Bilateral common-period theorem for two tensors.**

The proof chooses a common blocking period via `lcmPeriod` (on `Fin 2`), i.e. a
common multiple of `pA` and `pB`. The theorem statement itself only asserts the
existence of some positive period `p` for which both `blockTensor A p` and
`blockTensor B p` have primitive transfer maps.

If `A` and `B` are left-canonical (TP), then TP is preserved for this common
blocking. If `A` and `B` are normal, normality is also preserved for such a
common blocking period.

This is the building block for BNT canonical form alignment in subsequent
reduction steps; see issue #672 (Gap §1 step 2a). -/
theorem bilateral_commonPeriod_blocking_tp_primitive_normal
    {d D₁ D₂ : ℕ}
    [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (pA pB : ℕ) (hpA : 0 < pA) (hpB : 0 < pB)
    (hTPA : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hTPB : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hPrimA : _root_.IsPrimitive
      (transferMap (d := blockPhysDim d pA) (D := D₁)
        (blockTensor (d := d) (D := D₁) A pA)))
    (hPrimB : _root_.IsPrimitive
      (transferMap (d := blockPhysDim d pB) (D := D₂)
        (blockTensor (d := d) (D := D₂) B pB)))
    (hNormalA : IsNormal A) (hNormalB : IsNormal B) :
    ∃ p, 0 < p ∧
      _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := D₁)
          (blockTensor (d := d) (D := D₁) A p)) ∧
      _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := D₂)
          (blockTensor (d := d) (D := D₂) B p)) ∧
      (∑ i : Fin (blockPhysDim d p),
        (blockTensor (d := d) (D := D₁) A p i)ᴴ *
          blockTensor (d := d) (D := D₁) A p i = 1) ∧
      (∑ i : Fin (blockPhysDim d p),
        (blockTensor (d := d) (D := D₂) B p i)ᴴ *
          blockTensor (d := d) (D := D₂) B p i = 1) ∧
      IsNormal (d := blockPhysDim d p) (D := D₁)
        (blockTensor (d := d) (D := D₁) A p) ∧
      IsNormal (d := blockPhysDim d p) (D := D₂)
        (blockTensor (d := d) (D := D₂) B p) := by
  let periods : Fin 2 → ℕ := ![pA, pB]
  let p := lcmPeriod periods
  have hpPeriods : ∀ i : Fin 2, 0 < periods i := by
    intro i
    fin_cases i
    · exact hpA
    · exact hpB
  have hp : 0 < p := lcmPeriod_pos hpPeriods
  have hA_dvd : pA ∣ p := dvd_lcmPeriod periods 0
  have hB_dvd : pB ∣ p := by
    simpa [periods] using dvd_lcmPeriod periods 1
  have hPrimA' : _root_.IsPrimitive
      (transferMap (d := blockPhysDim d p) (D := D₁)
        (blockTensor (d := d) (D := D₁) A p)) :=
    isPrimitive_transferMap_blockTensor_of_dvd
      (d := d) (D := D₁) A pA p hA_dvd hp hPrimA
  have hPrimB' : _root_.IsPrimitive
      (transferMap (d := blockPhysDim d p) (D := D₂)
        (blockTensor (d := d) (D := D₂) B p)) :=
    isPrimitive_transferMap_blockTensor_of_dvd
      (d := d) (D := D₂) B pB p hB_dvd hp hPrimB
  refine ⟨p, hp, hPrimA', hPrimB', ?_, ?_, ?_, ?_⟩
  · exact leftCanonical_blockTensor (d := d) (D := D₁) (A := A) p hTPA
  · exact leftCanonical_blockTensor (d := d) (D := D₂) (A := B) p hTPB
  · exact isNormal_blockTensor_of_isNormal (d := d) (D := D₁) A hp hNormalA
  · exact isNormal_blockTensor_of_isNormal (d := d) (D := D₂) B hp hNormalB

/-- **Fundamental Theorem of MPS (1606.00608, after blocking): current structural shell.**

For any two MPS tensors `A, B` with `SameMPV₂ A B`, this theorem records the
currently formalized one-sided reduction output on both sides: after blocking,
each tensor admits a decomposition into TP blocks with primitive transfer maps,
nonzero weights, and positive bond dimensions.

The theorem does **not yet** use `SameMPV₂ A B` to compare the two blocked
outputs. The remaining missing content is the sector-level comparison
described in the file documentation below: a general BNT sector construction
for each side, followed by a heterogeneous equal-case comparison theorem for
those sector decompositions.

This theorem therefore records the structural shell currently available on the
way to arXiv:1606.00608, Theorem 1. -/
theorem fundamentalTheorem_after_blocking_1606_structural
    {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (_hSame : SameMPV₂ A B) :
    -- Both tensors have blocked TP-primitive decompositions
    ∃ (pA : ℕ) (_ : 0 < pA)
      (rA : ℕ) (dimA : Fin rA → ℕ) (μA : Fin rA → ℂ)
      (blocksA : (k : Fin rA) → MPSTensor (blockPhysDim d pA) (dimA k)),
    ∃ (pB : ℕ) (_ : 0 < pB)
      (rB : ℕ) (dimB : Fin rB → ℕ) (μB : Fin rB → ℂ)
      (blocksB : (k : Fin rB) → MPSTensor (blockPhysDim d pB) (dimB k)),
      -- Blocks are TP
      (∀ k, ∑ i, (blocksA k i)ᴴ * blocksA k i = 1) ∧
      (∀ k, ∑ i, (blocksB k i)ᴴ * blocksB k i = 1) ∧
      -- Blocks have primitive transfer maps
      (∀ k, _root_.IsPrimitive (transferMap (blocksA k))) ∧
      (∀ k, _root_.IsPrimitive (transferMap (blocksB k))) ∧
      -- Nonzero weights
      (∀ k, μA k ≠ 0) ∧
      (∀ k, μB k ≠ 0) ∧
      -- Positive bond dimensions
      (∀ k, 0 < dimA k) ∧
      (∀ k, 0 < dimB k) := by
  obtain ⟨_, pA, hpA, rA, dimA, μA, blocksA, hTPA, hPrimA, hDimA, hμA, _⟩ :=
    exists_tp_primitive_blockDecomp_after_blocking A
  obtain ⟨_, pB, hpB, rB, dimB, μB, blocksB, hTPB, hPrimB, hDimB, hμB, _⟩ :=
    exists_tp_primitive_blockDecomp_after_blocking B
  exact ⟨pA, hpA, rA, dimA, μA, blocksA, pB, hpB, rB, dimB, μB, blocksB,
    hTPA, hTPB, hPrimA, hPrimB, hμA, hμB, hDimA, hDimB⟩

/-- A strengthened after-blocking structural interface that keeps the blocked `SameMPV₂`
relations at the reduction periods. This is a small but genuine step toward Gap §1 because the
common-equality input is no longer discarded by the public structural theorem. -/
theorem fundamentalTheorem_after_blocking_1606_structural_with_blockedSameMPV₂
    {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B) :
    ∃ (pA : ℕ) (_ : 0 < pA)
      (rA : ℕ) (dimA : Fin rA → ℕ) (μA : Fin rA → ℂ)
      (blocksA : (k : Fin rA) → MPSTensor (blockPhysDim d pA) (dimA k)),
    ∃ (pB : ℕ) (_ : 0 < pB)
      (rB : ℕ) (dimB : Fin rB → ℕ) (μB : Fin rB → ℂ)
      (blocksB : (k : Fin rB) → MPSTensor (blockPhysDim d pB) (dimB k)),
      SameMPV₂ (blockTensor (d := d) (D := D₁) A pA)
        (blockTensor (d := d) (D := D₂) B pA) ∧
      SameMPV₂ (blockTensor (d := d) (D := D₁) A pB)
        (blockTensor (d := d) (D := D₂) B pB) ∧
      (∀ k, ∑ i, (blocksA k i)ᴴ * blocksA k i = 1) ∧
      (∀ k, ∑ i, (blocksB k i)ᴴ * blocksB k i = 1) ∧
      (∀ k, _root_.IsPrimitive (transferMap (blocksA k))) ∧
      (∀ k, _root_.IsPrimitive (transferMap (blocksB k))) ∧
      (∀ k, μA k ≠ 0) ∧
      (∀ k, μB k ≠ 0) ∧
      (∀ k, 0 < dimA k) ∧
      (∀ k, 0 < dimB k) := by
  obtain ⟨pA, hpA, rA, dimA, μA, blocksA, pB, hpB, rB, dimB, μB, blocksB,
    hTPA, hTPB, hPrimA, hPrimB, hμA, hμB, hDimA, hDimB⟩ :=
    fundamentalTheorem_after_blocking_1606_structural A B hSame
  refine ⟨pA, hpA, rA, dimA, μA, blocksA, pB, hpB, rB, dimB, μB, blocksB,
    ?_, ?_, hTPA, hTPB, hPrimA, hPrimB, hμA, hμB, hDimA, hDimB⟩
  · exact sameMPV₂_blockTensor A B hSame pA
  · exact sameMPV₂_blockTensor A B hSame pB

/-- **Conditional after-blocking sector endpoint (issue #877 target shape).**

Given two tensors with `SameMPV₂`, a common-period BNT sector pair, and a
matched-basis extractor, this theorem produces the target assembly conclusion: a
common blocking period, a `SectorDecomposition` on each side carrying BNT basis
data, and matched sector-weight data for the canonical-form reduction.

The two hypotheses are intentionally separated:

* `bntSectorPair` supplies a common-period BNT sector decomposition for both
  sides, `SameMPV₂`-equivalent to the blocked tensors and carrying
  `HasBNTSectorData`.
* `matchedBasisData` supplies the matched-basis witness (permutation, copy
  alignment, per-block gauge-phase equivalence) from `SameMPV₂` between two
  sector decompositions whose first entry has BNT basis data.

The body is a kernel-checked composition of the existing structural theorem's
blocking compatibility (`sameMPV₂_blockTensor`), the two hypotheses, and the
matched-basis algebraic endpoint from PR #844
(`fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_matched_basis`).  The
later theorems below instantiate the matching side with primitive overlap-span
hypotheses rather than assuming the witness directly. -/
theorem fundamentalTheorem_after_blocking_1606_sector_of_bntPair_matched
    {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B)
    (bntSectorPair :
      ∃ p : ℕ, 0 < p ∧
      ∃ P Q : SectorDecomposition (blockPhysDim d p),
        SameMPV₂ (blockTensor (d := d) (D := D₁) A p) P.toTensor ∧
        SameMPV₂ (blockTensor (d := d) (D := D₂) B p) Q.toTensor ∧
        HasBNTSectorData P ∧ HasBNTSectorData Q)
    (matchedBasisData : ∀ {d' : ℕ} (P Q : SectorDecomposition d'),
      HasBNTSectorData P → SameMPV₂ P.toTensor Q.toTensor →
      ∃ perm : Fin P.basisCount ≃ Fin Q.basisCount,
        (∀ j, P.copies j = Q.copies (perm j)) ∧
        ∀ j : Fin P.basisCount,
          ∃ hdim : P.basisDim j = Q.basisDim (perm j),
            GaugePhaseEquiv (d := d')
              (cast (congr_arg (MPSTensor d') hdim) (P.basis j))
              (Q.basis (perm j))) :
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
  obtain ⟨p, hp, P, Q, hPeq, hQeq, hPbnt, hQbnt⟩ := bntSectorPair
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
  obtain ⟨perm, hCopies, hBasisGPE⟩ := matchedBasisData P Q hPbnt hPQeq
  obtain ⟨ζ, hζne, hMultiset⟩ :=
    fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_matched_basis
      P Q perm hCopies hBasisGPE hPbnt hPQeq
  exact ⟨p, hp, P, Q, hPeq, hQeq, hPbnt, hQbnt,
          perm, hCopies, ζ, hζne, hMultiset⟩


/-- **After-blocking sector endpoint from primitive overlap-span data.**

This theorem replaces the abstract `matchedBasisData` hypothesis in
`fundamentalTheorem_after_blocking_1606_sector_of_bntPair_matched` by the
paper-level overlap-rigidity inputs collected in
`SectorBasisOverlapSpanHypotheses`.  The hypotheses still include a BNT sector
pair at a common blocking period, but the matching witness itself is now
constructed by `SectorBasisOverlapSpanHypotheses.exists_sectorBasisMatching` and
then fed to the bundled heterogeneous sector comparison theorem.

Thus the theorem wires the post-#860 comparison machinery without assuming a
`SectorBasisMatching` or a permutation/copy alignment as input. -/
theorem fundamentalTheorem_after_blocking_1606_sector_of_bntPair_overlapSpan
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

/-- **Common live-block assembly using the one-sided BNT construction.**

Assume a common blocking period `p` has already produced exact live block
decompositions of `blockTensor A p` and `blockTensor B p` by TP primitive
irreducible blocks with nonzero weights.  The theorem applies the collapsed
one-sided BNT construction
`exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks` on both sides, derives the
equality of the two resulting sector tensors from the original `SameMPV₂ A B`,
and then uses primitive overlap-span data for the constructed sector bases to
produce the matched sector-weight conclusion.

The remaining work for the fully unconditional theorem is to obtain these exact
common live-block decompositions, and the overlap-span data for their collapsed
BNT sector bases, from the current structural reduction without extra
hypotheses. -/
theorem fundamentalTheorem_after_blocking_1606_sector_of_common_blocks_overlapSpan
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

/-!
### What remains for the full 1606.00608 Fundamental Theorem

The complete end-to-end FT should take two tensors `A, B` with `SameMPV₂ A B`
and pass from the blocked reduction output to the paper's basis-of-normal-tensors
sector comparison.  The one-sided collapsed BNT construction is now available as
`exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks`, and the sector matching
extraction is available from primitive overlap-rigidity hypotheses through
`SectorBasisOverlapSpanHypotheses.exists_sectorBasisMatching`.

The theorem
`fundamentalTheorem_after_blocking_1606_sector_of_common_blocks_overlapSpan`
records the strongest assembled Lean statement currently available: once a common
blocking period gives exact live TP primitive irreducible block decompositions on
both sides, the one-sided BNT construction and the overlap-span matching theorem
produce the matched sector-weight conclusion from the original `SameMPV₂ A B`.

The remaining formal work for the completely unconditional
`fundamentalTheorem_after_blocking_1606_sector` is therefore not another matched
basis assumption.  It is to derive, from the structural reduction itself:

1. a common live block decomposition with primitive **and irreducible** blocks at
   the same physical blocking level, with the zero-tail contribution handled at
   `N = 0`;
2. the nonzero-bond-dimension, injectivity, normalization, asymptotic
   self/orthogonal-overlap, and finite-length span hypotheses bundled in
   `SectorBasisOverlapSpanHypotheses` for the collapsed BNT bases produced by
   `exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks`; and
3. the final global gauge construction of the equal-case FT after the matched
   sector-weight data has been obtained.

Thus the common-period arithmetic and the abstract sector-matching witness are no
longer the main blockers; the remaining gap is the paper-level derivation of the
primitive overlap-span hypotheses for the actual collapsed BNT bases, together
with the live/zero-tail bookkeeping needed to compare the sector tensors as full
`SameMPV₂` families.
-/

end FundamentalTheorem1606

end MPSTensor

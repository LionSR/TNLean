/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.Assembly.CommonSectorData

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Filter

/-!
# Structural after-blocking theorem for canonical-form reduction

This file collects the final structural statements in the current
canonical-form reduction following arXiv:1606.00608. It gives a common-period blocking theorem
for two tensors and the resulting structural after-blocking statement that both
sides have TP-primitive decompositions.

## Main statements

* `bilateral_commonPeriod_blocking_tp_primitive_normal` — two tensors with
  primitive blocked transfer maps have a common positive blocking period that
  preserves primitivity, left-canonical normalization, and normality.
* `exists_bilateral_tp_primitive_blockDecomp_after_blocking` — two tensors
  have blocked TP-primitive decompositions on both sides.

## References

* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608, Section 2.3 + Appendix A]
* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:2011.12127, Section IV]

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

The full proof chain is:
1. Zero-block separation (`exists_irreducible_blockDecomp_nonzeroBlocks`)
2. TP gauge (`exists_tp_gauge_from_arbitrary_with_zeroTail`)
3. Common blocking to primitive (`exists_common_blocking_all_primitive_of_TP_irr`)
4. Cyclic sector decomposition per block (`exists_cyclic_sector_decomp_after_blocking`)

### Remaining mathematical inputs

The theorem `exists_tp_sector_decomp_after_blocking` below provides:
- A blocking period `p > 0`
- A trivial block of dimension `zeroTailDim`
- A family of TP sector blocks
- The MPV relationship: `blockTensor A p` is `SameMPV₂`-equivalent to
  `zeroMPSTensor + toTensorFromBlocks μ sectors` for some weights `μ`

The current library already settles the common-period blocking arithmetic and
now has a one-sided phase-class BNT construction for TP primitive irreducible
nonzero-weight blocks, one-sided overlap data, and witness-producing sector comparison
from primitive overlap-span hypotheses. The theorem
`afterBlocking_perBlockCyclicDataWithZeroTail_of_sameMPV₂`
keeps the faithful paper order: first split off the zero tail and TP-gauge the
irreducible nonzero-weight blocks, then remove each block's period by cyclic sectors.
It deliberately does not identify that period-removal length with the later
finite blocking length used for common refinement or injectivity.

The nonzero-part theorem
`fundamentalTheorem_after_blocking_sector_of_common_blocks_injectiveSpan`
uses a two-basis span comparison for the constructed sector bases, while
`fundamentalTheorem_after_blocking_sector_of_common_blocks_blockSpan`
transports a finite-length span equality for the original nonzero-weight block families to
those bases. The zero-tail-aware theorem
`fundamentalTheorem_after_blocking_sector_of_common_blocks_overlapSpan_zeroTail`
separately gives the length-zero identity when full overlap-span hypotheses are
available.

The subsequent common-sector step flattens the per-block cyclic-sector data to a
single common physical blocking level. The remaining paper-level inputs are
one-site injectivity (or a blocked replacement), finite-length span comparison
for the flattened family, and the zero-tail length-zero identity from the
structural after-blocking reduction itself.
-/

section FundamentalTheoremAfterBlocking

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
reduction steps. -/
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

/-- **Bilateral one-sided structural decomposition after blocking.**

For any two MPS tensors `A, B`, this theorem gives the one-sided reduction data
on both sides: after blocking, each tensor admits a decomposition into a
zero-tail tensor and TP blocks with primitive transfer maps, nonzero weights,
and positive bond dimensions.

This theorem intentionally has no `SameMPV₂ A B` hypothesis: it does not compare
the two blocked families. The comparison enters only in later statements that
also keep blocked `SameMPV₂` data. -/
lemma exists_bilateral_tp_primitive_blockDecomp_after_blocking
    {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) :
    -- Both tensors have blocked TP-primitive decompositions
    ∃ (zeroTailA : ℕ) (pA : ℕ) (_ : 0 < pA)
      (rA : ℕ) (dimA : Fin rA → ℕ) (μA : Fin rA → ℂ)
      (blocksA : (k : Fin rA) → MPSTensor (blockPhysDim d pA) (dimA k)),
    ∃ (zeroTailB : ℕ) (pB : ℕ) (_ : 0 < pB)
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
      (∀ k, 0 < dimB k) ∧
      -- MPV decomposition equations
      (∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d pA)),
        mpv (blockTensor (d := d) (D := D₁) A pA) σ =
          mpv (zeroMPSTensor (blockPhysDim d pA) zeroTailA) σ +
            mpv (toTensorFromBlocks (d := blockPhysDim d pA) (μ := μA) blocksA) σ) ∧
      (∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d pB)),
        mpv (blockTensor (d := d) (D := D₂) B pB) σ =
          mpv (zeroMPSTensor (blockPhysDim d pB) zeroTailB) σ +
            mpv (toTensorFromBlocks (d := blockPhysDim d pB) (μ := μB) blocksB) σ) := by
  obtain ⟨zeroTailA, pA, hpA, rA, dimA, μA, blocksA,
    hTPA, hPrimA, hDimA, hμA, hMPVA⟩ :=
    exists_tp_primitive_blockDecomp_after_blocking A
  obtain ⟨zeroTailB, pB, hpB, rB, dimB, μB, blocksB,
    hTPB, hPrimB, hDimB, hμB, hMPVB⟩ :=
    exists_tp_primitive_blockDecomp_after_blocking B
  exact ⟨zeroTailA, pA, hpA, rA, dimA, μA, blocksA,
    zeroTailB, pB, hpB, rB, dimB, μB, blocksB,
    hTPA, hTPB, hPrimA, hPrimB, hμA, hμB, hDimA, hDimB, hMPVA, hMPVB⟩

/-- A strengthened after-blocking structural statement that keeps the blocked `SameMPV₂`
relations at the reduction periods. This is a genuine step forward because the
common equality is no longer discarded by the public structural theorem. -/
theorem afterBlocking_structuralDataWithBlockedSameMPV₂_of_sameMPV₂
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
  obtain ⟨_zeroTailA, pA, hpA, rA, dimA, μA, blocksA,
    _zeroTailB, pB, hpB, rB, dimB, μB, blocksB,
    hTPA, hTPB, hPrimA, hPrimB, hμA, hμB, hDimA, hDimB, _hMPVA, _hMPVB⟩ :=
    exists_bilateral_tp_primitive_blockDecomp_after_blocking A B
  refine ⟨pA, hpA, rA, dimA, μA, blocksA, pB, hpB, rB, dimB, μB, blocksB,
    ?_, ?_, hTPA, hTPB, hPrimA, hPrimB, hμA, hμB, hDimA, hDimB⟩
  · exact sameMPV₂_blockTensor A B hSame pA
  · exact sameMPV₂_blockTensor A B hSame pB

/-- **Structural after-blocking theorem retaining zero-tail MPV equations.**

This strengthens the structural shell by exposing the exact zero-tail identities
returned by `exists_tp_primitive_blockDecomp_after_blocking`, in addition to the
blocked `SameMPV₂` relations. The nonzero-weight blocks are trace-preserving, have
primitive transfer maps, positive bond dimensions, and nonzero weights; the
zero-tail equations explain precisely why these nonzero parts are only immediately
identified at positive lengths unless the `N = 0` zero-tail identity is also
resolved. -/
theorem afterBlocking_tpPrimitiveBlockDecompositions_of_sameMPV₂
    {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B) :
    ∃ (zeroTailA : ℕ) (pA : ℕ) (_ : 0 < pA)
      (rA : ℕ) (dimA : Fin rA → ℕ) (μA : Fin rA → ℂ)
      (blocksA : (k : Fin rA) → MPSTensor (blockPhysDim d pA) (dimA k)),
    ∃ (zeroTailB : ℕ) (pB : ℕ) (_ : 0 < pB)
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
      (∀ k, 0 < dimB k) ∧
      (∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d pA)),
        mpv (blockTensor (d := d) (D := D₁) A pA) σ =
          mpv (zeroMPSTensor (blockPhysDim d pA) zeroTailA) σ +
            mpv (toTensorFromBlocks (d := blockPhysDim d pA) (μ := μA) blocksA) σ) ∧
      (∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d pB)),
        mpv (blockTensor (d := d) (D := D₂) B pB) σ =
          mpv (zeroMPSTensor (blockPhysDim d pB) zeroTailB) σ +
            mpv (toTensorFromBlocks (d := blockPhysDim d pB) (μ := μB) blocksB) σ) := by
  obtain ⟨zeroTailA, pA, hpA, rA, dimA, μA, blocksA, hTPA, hPrimA, hDimA, hμA, hMPVA⟩ :=
    exists_tp_primitive_blockDecomp_after_blocking A
  obtain ⟨zeroTailB, pB, hpB, rB, dimB, μB, blocksB, hTPB, hPrimB, hDimB, hμB, hMPVB⟩ :=
    exists_tp_primitive_blockDecomp_after_blocking B
  refine ⟨zeroTailA, pA, hpA, rA, dimA, μA, blocksA,
    zeroTailB, pB, hpB, rB, dimB, μB, blocksB,
    ?_, ?_, hTPA, hTPB, hPrimA, hPrimB, hμA, hμB, hDimA, hDimB, hMPVA, hMPVB⟩
  · exact sameMPV₂_blockTensor A B hSame pA
  · exact sameMPV₂_blockTensor A B hSame pB


end FundamentalTheoremAfterBlocking

end MPSTensor

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.Assembly.CommonBlockedCyclicSectorConstruction
import TNLean.MPS.CanonicalForm.Assembly.ZeroTailTransport
import TNLean.MPS.CanonicalForm.EqualNormBridge

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
* `afterBlocking_structuralData_of_sameMPV₂` — two tensors with the
  same MPVs have blocked TP-primitive decompositions on both sides.

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

The remaining content is to flatten the per-block cyclic-sector data to a
single common physical blocking level, derive one-site injectivity (or a blocked
replacement) and the finite-length span comparison for the flattened family, and
finish the zero-tail length-zero identity from the structural after-blocking reduction
itself.
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

/-- **Fundamental Theorem of MPS (1606.00608, after blocking): current structural shell.**

For any two MPS tensors `A, B` with `SameMPV₂ A B`, this theorem gives the
currently formalized one-sided reduction data on both sides: after blocking,
each tensor admits a decomposition into a zero-tail tensor and TP blocks with
primitive transfer maps, nonzero weights, and positive bond dimensions.

The theorem does not yet use `SameMPV₂ A B` to compare the two blocked
families. The subsequent content is the sector-level comparison:
a BNT sector construction for each side,
followed by a two-basis equal-case comparison theorem for those sector decompositions.

This theorem therefore gives the structural statement currently available on the
way to arXiv:1606.00608, Theorem 1. -/
theorem afterBlocking_structuralDecompositionData_of_sameMPV₂
    {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (_hSame : SameMPV₂ A B) :
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

/-- Compatibility formulation for the older structural data shape.

This keeps the historical witness order while the stronger decomposition version
`afterBlocking_structuralDecompositionData_of_sameMPV₂` exposes the zero-tail MPV
equations needed for the paper-facing statement. -/
theorem afterBlocking_structuralData_of_sameMPV₂
    {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B) :
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
  obtain ⟨_zeroTailA, pA, hpA, rA, dimA, μA, blocksA,
    _zeroTailB, pB, hpB, rB, dimB, μB, blocksB,
    hTPA, hTPB, hPrimA, hPrimB, hμA, hμB, hDimA, hDimB, _hMPVA, _hMPVB⟩ :=
    afterBlocking_structuralDecompositionData_of_sameMPV₂ A B hSame
  exact ⟨pA, hpA, rA, dimA, μA, blocksA, pB, hpB, rB, dimB, μB, blocksB,
    hTPA, hTPB, hPrimA, hPrimB, hμA, hμB, hDimA, hDimB⟩

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
  obtain ⟨pA, hpA, rA, dimA, μA, blocksA,
    pB, hpB, rB, dimB, μB, blocksB,
    hTPA, hTPB, hPrimA, hPrimB, hμA, hμB, hDimA, hDimB⟩ :=
    afterBlocking_structuralData_of_sameMPV₂ A B hSame
  refine ⟨pA, hpA, rA, dimA, μA, blocksA, pB, hpB, rB, dimB, μB, blocksB,
    ?_, ?_, hTPA, hTPB, hPrimA, hPrimB, hμA, hμB, hDimA, hDimB⟩
  · exact sameMPV₂_blockTensor A B hSame pA
  · exact sameMPV₂_blockTensor A B hSame pB

/-- **Zero-tail identity for nonzero block tensors.**

Suppose two tensors with the same MPV family are each written as a zero-tail
contribution plus a weighted nonzero block tensor. Then the nonzero parts agree at every
positive length, while the length-zero equation gives exactly the difference
between the zero-tail dimensions and the nonzero block bond dimensions.

This is the local length-zero identity needed before a full `SameMPV₂` comparison of the
nonzero block tensors can be recovered: the only missing datum is equality of the
two zero-tail dimensions (or an equivalent replacement for the `N = 0` case). -/
theorem nonzeroBlock_positive_sameMPV₂_and_zeroTail_identity_of_sameMPV₂
    {d D₁ D₂ rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B)
    (zeroTailA zeroTailB : ℕ)
    (μA : Fin rA → ℂ) (blocksA : (k : Fin rA) → MPSTensor d (dimA k))
    (μB : Fin rB → ℂ) (blocksB : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv A σ = mpv (zeroMPSTensor d zeroTailA) σ +
        mpv (toTensorFromBlocks (d := d) (μ := μA) blocksA) σ)
    (hB : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv B σ = mpv (zeroMPSTensor d zeroTailB) σ +
        mpv (toTensorFromBlocks (d := d) (μ := μB) blocksB) σ) :
    (∀ {N : ℕ}, 0 < N → ∀ σ : Fin N → Fin d,
      mpv (toTensorFromBlocks (d := d) (μ := μA) blocksA) σ =
        mpv (toTensorFromBlocks (d := d) (μ := μB) blocksB) σ) ∧
    (∀ σ : Fin 0 → Fin d,
      (zeroTailA : ℂ) + mpv (toTensorFromBlocks (d := d) (μ := μA) blocksA) σ =
        (zeroTailB : ℂ) + mpv (toTensorFromBlocks (d := d) (μ := μB) blocksB) σ) := by
  constructor
  · intro N hN σ
    have hN_ne : N ≠ 0 := Nat.ne_of_gt hN
    have hAσ := hA N σ
    have hBσ := hB N σ
    rw [mpv_zeroMPSTensor, if_neg hN_ne, zero_add] at hAσ
    rw [mpv_zeroMPSTensor, if_neg hN_ne, zero_add] at hBσ
    calc
      mpv (toTensorFromBlocks (d := d) (μ := μA) blocksA) σ = mpv A σ := hAσ.symm
      _ = mpv B σ := hSame N σ
      _ = mpv (toTensorFromBlocks (d := d) (μ := μB) blocksB) σ := hBσ
  · intro σ
    have hAσ := hA 0 σ
    have hBσ := hB 0 σ
    rw [mpv_zeroMPSTensor, if_pos rfl] at hAσ
    rw [mpv_zeroMPSTensor, if_pos rfl] at hBσ
    calc
      (zeroTailA : ℂ) + mpv (toTensorFromBlocks (d := d) (μ := μA) blocksA) σ
          = mpv A σ := hAσ.symm
      _ = mpv B σ := hSame 0 σ
      _ = (zeroTailB : ℂ) + mpv (toTensorFromBlocks (d := d) (μ := μB) blocksB) σ := hBσ

/-- **Reblocked nonzero-block equality with a zero-tail identity.**

If two tensors have the same MPVs and each is expressed as a zero tail plus a
weighted nonzero block tensor, then every positive common reblocking transports the
nonzero weights to powers, preserves positive-length equality of the nonzero parts,
and leaves the zero-tail contribution as the sole length-zero term. -/
theorem nonzeroBlock_blockPower_positive_sameMPV₂_and_zeroTail_identity_of_sameMPV₂
    {d D₁ D₂ rA rB p : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B)
    (zeroTailA zeroTailB : ℕ)
    (μA : Fin rA → ℂ) (blocksA : (k : Fin rA) → MPSTensor d (dimA k))
    (μB : Fin rB → ℂ) (blocksB : (k : Fin rB) → MPSTensor d (dimB k))
    (hp : 0 < p)
    (hA : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv A σ = mpv (zeroMPSTensor d zeroTailA) σ +
        mpv (toTensorFromBlocks (d := d) (μ := μA) blocksA) σ)
    (hB : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv B σ = mpv (zeroMPSTensor d zeroTailB) σ +
        mpv (toTensorFromBlocks (d := d) (μ := μB) blocksB) σ) :
    SameMPV₂Pos
      (toTensorFromBlocks (d := blockPhysDim d p)
        (fun k => (μA k) ^ p)
        (fun k => blockTensor (d := d) (D := dimA k) (blocksA k) p))
      (toTensorFromBlocks (d := blockPhysDim d p)
        (fun k => (μB k) ^ p)
        (fun k => blockTensor (d := d) (D := dimB k) (blocksB k) p)) ∧
    (∀ σ : Fin 0 → Fin (blockPhysDim d p),
      (zeroTailA : ℂ) +
          mpv (toTensorFromBlocks (d := blockPhysDim d p)
            (fun k => (μA k) ^ p)
            (fun k => blockTensor (d := d) (D := dimA k) (blocksA k) p)) σ =
        (zeroTailB : ℂ) +
          mpv (toTensorFromBlocks (d := blockPhysDim d p)
            (fun k => (μB k) ^ p)
            (fun k => blockTensor (d := d) (D := dimB k) (blocksB k) p)) σ) := by
  have hAblock :=
    zeroTail_toTensorFromBlocks_blockPower
      (d := d) (D := D₁) (r := rA) (z := zeroTailA) (p := p) (dim := dimA)
      A μA blocksA hp hA
  have hBblock :=
    zeroTail_toTensorFromBlocks_blockPower
      (d := d) (D := D₂) (r := rB) (z := zeroTailB) (p := p) (dim := dimB)
      B μB blocksB hp hB
  have hAB : SameMPV₂ (blockTensor (d := d) (D := D₁) A p)
      (blockTensor (d := d) (D := D₂) B p) :=
    sameMPV₂_blockTensor A B hSame p
  have hBook :=
    nonzeroBlock_positive_sameMPV₂_and_zeroTail_identity_of_sameMPV₂
      (d := blockPhysDim d p)
      (blockTensor (d := d) (D := D₁) A p)
      (blockTensor (d := d) (D := D₂) B p)
      hAB zeroTailA zeroTailB
      (fun k => (μA k) ^ p)
      (fun k => blockTensor (d := d) (D := dimA k) (blocksA k) p)
      (fun k => (μB k) ^ p)
      (fun k => blockTensor (d := d) (D := dimB k) (blocksB k) p)
      hAblock hBblock
  exact ⟨fun N hN σ => hBook.1 hN σ, hBook.2⟩

/-- **Recover full nonzero-block `SameMPV₂` once zero tails agree.**

This combines the positive-length theorem with the single additional
length-zero datum needed to remove the zero tails. It does not assert that the
zero-tail dimensions agree automatically; that remains a separate paper-level
length-zero condition for the unconditional after-blocking sector comparison. -/
theorem nonzeroBlock_sameMPV₂_of_sameMPV₂_of_zeroTail_eq
    {d D₁ D₂ rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B)
    (zeroTailA zeroTailB : ℕ)
    (μA : Fin rA → ℂ) (blocksA : (k : Fin rA) → MPSTensor d (dimA k))
    (μB : Fin rB → ℂ) (blocksB : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv A σ = mpv (zeroMPSTensor d zeroTailA) σ +
        mpv (toTensorFromBlocks (d := d) (μ := μA) blocksA) σ)
    (hB : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv B σ = mpv (zeroMPSTensor d zeroTailB) σ +
        mpv (toTensorFromBlocks (d := d) (μ := μB) blocksB) σ)
    (hZeroTail : zeroTailA = zeroTailB) :
    SameMPV₂ (toTensorFromBlocks (d := d) (μ := μA) blocksA)
      (toTensorFromBlocks (d := d) (μ := μB) blocksB) := by
  have hBook :=
    nonzeroBlock_positive_sameMPV₂_and_zeroTail_identity_of_sameMPV₂
      A B hSame zeroTailA zeroTailB μA blocksA μB blocksB hA hB
  intro N σ
  by_cases hN : N = 0
  · subst N
    have h0 := hBook.2 σ
    have h0' : (zeroTailB : ℂ) +
        mpv (toTensorFromBlocks (d := d) (μ := μA) blocksA) σ =
        (zeroTailB : ℂ) +
        mpv (toTensorFromBlocks (d := d) (μ := μB) blocksB) σ := by
      simpa [hZeroTail] using h0
    exact add_left_cancel h0'
  · exact hBook.1 (Nat.pos_of_ne_zero hN) σ

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

/-- **Per-block cyclic-sector decomposition with a zero-tail identity.**

This is the faithful predecessor to the common nonzero-sector statement. From
`SameMPV₂ A B`, it first uses the invariant-subspace/zero-tail split and TP gauge
to obtain irreducible nonzero-weight blocks on both sides. It then removes the period of
each block separately, producing primitive irreducible cyclic sectors for
every nonzero-weight block. The nonzero parts agree at positive lengths, and the length-zero
case is given as the explicit zero-tail identity.

The theorem intentionally keeps the per-block period-removal lengths inside
`HasPrimitiveIrreducibleCyclicSectors`. It does not conflate those lengths with a
later common-refinement or Wielandt/injectivity blocking length; assembling the
per-block cyclic sectors at one physical blocking level is the next formal
statement in the reduction chain. -/
theorem afterBlocking_perBlockCyclicDataWithZeroTail_of_sameMPV₂
    {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B) :
    ∃ (zeroTailA : ℕ) (rA : ℕ) (dimA : Fin rA → ℕ) (μA : Fin rA → ℂ)
      (blocksA : (k : Fin rA) → MPSTensor d (dimA k)),
    ∃ (zeroTailB : ℕ) (rB : ℕ) (dimB : Fin rB → ℕ) (μB : Fin rB → ℂ)
      (blocksB : (k : Fin rB) → MPSTensor d (dimB k)),
      (∀ k, IsIrreducibleTensor (blocksA k)) ∧
      (∀ k, IsIrreducibleTensor (blocksB k)) ∧
      (∀ k, ∑ i : Fin d, (blocksA k i)ᴴ * blocksA k i = 1) ∧
      (∀ k, ∑ i : Fin d, (blocksB k i)ᴴ * blocksB k i = 1) ∧
      (∀ k, μA k ≠ 0) ∧
      (∀ k, μB k ≠ 0) ∧
      (∀ k, 0 < dimA k) ∧
      (∀ k, 0 < dimB k) ∧
      (∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv A σ = mpv (zeroMPSTensor d zeroTailA) σ +
          mpv (toTensorFromBlocks (d := d) (μ := μA) blocksA) σ) ∧
      (∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv B σ = mpv (zeroMPSTensor d zeroTailB) σ +
          mpv (toTensorFromBlocks (d := d) (μ := μB) blocksB) σ) ∧
      SameMPV₂Pos
        (toTensorFromBlocks (d := d) (μ := μA) blocksA)
        (toTensorFromBlocks (d := d) (μ := μB) blocksB) ∧
      (∀ σ : Fin 0 → Fin d,
        (zeroTailA : ℂ) + mpv (toTensorFromBlocks (d := d) (μ := μA) blocksA) σ =
          (zeroTailB : ℂ) + mpv (toTensorFromBlocks (d := d) (μ := μB) blocksB) σ) ∧
      (∀ k, HasPrimitiveIrreducibleCyclicSectors (blocksA k)) ∧
      (∀ k, HasPrimitiveIrreducibleCyclicSectors (blocksB k)) := by
  obtain ⟨zeroTailA, rA, dimA, μA, blocksA,
      hIrrA, hTPA, hμA, hDimA, hMPVA⟩ :=
    exists_tp_gauge_from_arbitrary_with_zeroTail (d := d) (D := D₁) A
  obtain ⟨zeroTailB, rB, dimB, μB, blocksB,
      hIrrB, hTPB, hμB, hDimB, hMPVB⟩ :=
    exists_tp_gauge_from_arbitrary_with_zeroTail (d := d) (D := D₂) B
  have hBook :=
    nonzeroBlock_positive_sameMPV₂_and_zeroTail_identity_of_sameMPV₂
      A B hSame zeroTailA zeroTailB μA blocksA μB blocksB hMPVA hMPVB
  refine ⟨zeroTailA, rA, dimA, μA, blocksA,
    zeroTailB, rB, dimB, μB, blocksB,
    hIrrA, hIrrB, hTPA, hTPB, hμA, hμB, hDimA, hDimB, hMPVA, hMPVB,
    ?_, hBook.2, ?_, ?_⟩
  · intro N hN σ
    exact hBook.1 hN σ
  · intro k
    letI : NeZero (dimA k) := ⟨Nat.ne_of_gt (hDimA k)⟩
    exact hasPrimitiveIrreducibleCyclicSectors_of_TP_of_isIrreducibleTensor
      (blocksA k) (hTPA k) (hIrrA k)
  · intro k
    letI : NeZero (dimB k) := ⟨Nat.ne_of_gt (hDimB k)⟩
    exact hasPrimitiveIrreducibleCyclicSectors_of_TP_of_isIrreducibleTensor
      (blocksB k) (hTPB k) (hIrrB k)

/-- **Common-blocking predecessor for nonzero cyclic sectors with a zero-tail identity.**

This theorem combines the zero-tail/TP-gauge reduction for nonzero-weight blocks with the common
reblocking constructor for per-block cyclic sectors.  The theorem asserts the
existence of the original nonzero-weight block families on both sides and, for each side, a
finite flattened sector family at the corresponding common blocked physical
dimension.  The flattened sectors are trace-preserving, have primitive transfer
maps, are tensor-irreducible, have positive bond dimensions, and carry nonzero
unit weights.  The statement keeps the checked zero-tail equations,
positive-length equality of the nonzero parts, and the length-zero identity at the unblocked
nonzero-block level.  The companion theorem
`afterBlocking_reindexedCommonSectorDataWithZeroTail_of_sameMPV₂`
adds the explicitly relabeled cyclic-sector flattening available after
the iterated-blocking comparison theorem. -/
theorem afterBlocking_commonBlockedCyclicDataWithZeroTail_of_sameMPV₂
    {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B) :
    ∃ (zeroTailA : ℕ) (rA : ℕ) (dimA : Fin rA → ℕ) (μA : Fin rA → ℂ)
      (blocksA : (k : Fin rA) → MPSTensor d (dimA k)),
    ∃ (zeroTailB : ℕ) (rB : ℕ) (dimB : Fin rB → ℕ) (μB : Fin rB → ℂ)
      (blocksB : (k : Fin rB) → MPSTensor d (dimB k)),
    ∃ (familyA : CommonBlockedCyclicSectorFamily blocksA),
    ∃ (familyB : CommonBlockedCyclicSectorFamily blocksB),
      (∀ k, IsIrreducibleTensor (blocksA k)) ∧
      (∀ k, IsIrreducibleTensor (blocksB k)) ∧
      (∀ k, ∑ i : Fin d, (blocksA k i)ᴴ * blocksA k i = 1) ∧
      (∀ k, ∑ i : Fin d, (blocksB k i)ᴴ * blocksB k i = 1) ∧
      (∀ k, μA k ≠ 0) ∧
      (∀ k, μB k ≠ 0) ∧
      (∀ k, 0 < dimA k) ∧
      (∀ k, 0 < dimB k) ∧
      (∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv A σ = mpv (zeroMPSTensor d zeroTailA) σ +
          mpv (toTensorFromBlocks (d := d) (μ := μA) blocksA) σ) ∧
      (∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv B σ = mpv (zeroMPSTensor d zeroTailB) σ +
          mpv (toTensorFromBlocks (d := d) (μ := μB) blocksB) σ) ∧
      SameMPV₂Pos
        (toTensorFromBlocks (d := d) (μ := μA) blocksA)
        (toTensorFromBlocks (d := d) (μ := μB) blocksB) ∧
      (∀ σ : Fin 0 → Fin d,
        (zeroTailA : ℂ) + mpv (toTensorFromBlocks (d := d) (μ := μA) blocksA) σ =
          (zeroTailB : ℂ) + mpv (toTensorFromBlocks (d := d) (μ := μB) blocksB) σ) ∧
      (∀ x, familyA.flatWeight x ≠ 0) ∧
      (∀ x, familyB.flatWeight x ≠ 0) := by
  obtain ⟨zeroTailA, rA, dimA, μA, blocksA,
      zeroTailB, rB, dimB, μB, blocksB,
      hIrrA, hIrrB, hTPA, hTPB, hμA, hμB, hDimA, hDimB,
      hMPVA, hMPVB, hPos, hZero, hCycA, hCycB⟩ :=
    afterBlocking_perBlockCyclicDataWithZeroTail_of_sameMPV₂ A B hSame
  obtain ⟨familyA⟩ :=
    exists_commonBlockedCyclicSectorFamily_of_hasPrimitiveIrreducibleCyclicSectors
      blocksA hCycA
  obtain ⟨familyB⟩ :=
    exists_commonBlockedCyclicSectorFamily_of_hasPrimitiveIrreducibleCyclicSectors
      blocksB hCycB
  refine ⟨zeroTailA, rA, dimA, μA, blocksA,
    zeroTailB, rB, dimB, μB, blocksB, familyA, familyB,
    hIrrA, hIrrB, hTPA, hTPB, hμA, hμB, hDimA, hDimB,
    hMPVA, hMPVB, hPos, hZero, ?_, ?_⟩
  · intro x
    exact familyA.flatWeight_ne_zero x
  · intro x
    exact familyB.flatWeight_ne_zero x

/-- **Relabeled common-sector data with zero-tail reblocking.**

This companion to
`afterBlocking_commonBlockedCyclicDataWithZeroTail_of_sameMPV₂`
uses the common cyclic-sector family to express the reindexed block data available
after the iterated-blocking comparison theorem.  For each side, the cyclic
sectors are expressed as derived common-alphabet blocks `family.commonFlatBlocks`,
with weights `μ^family.p` and
nonzero transported sector weights.  The theorem also gives the zero-tail
identities after the corresponding common reblocking.

The statement is deliberately explicit about the reindexing of blocked physical
words: the relabeled block field is the block `B_k^[family.p]` after applying
`iteratedBlockIndex`.  It does not assert that the canonical blocked family and
the per-block reindexed family are identical as physical-word indexed tensors. -/
theorem afterBlocking_reindexedCommonSectorDataWithZeroTail_of_sameMPV₂
    {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B) :
    ∃ (zeroTailA : ℕ) (rA : ℕ) (dimA : Fin rA → ℕ) (μA : Fin rA → ℂ)
      (blocksA : (k : Fin rA) → MPSTensor d (dimA k)),
    ∃ (zeroTailB : ℕ) (rB : ℕ) (dimB : Fin rB → ℕ) (μB : Fin rB → ℂ)
      (blocksB : (k : Fin rB) → MPSTensor d (dimB k)),
    ∃ (familyA : CommonBlockedCyclicSectorFamily blocksA),
    ∃ (familyB : CommonBlockedCyclicSectorFamily blocksB),
      (∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d familyA.p)),
        mpv (blockTensor (d := d) (D := D₁) A familyA.p) σ =
          mpv (zeroMPSTensor (blockPhysDim d familyA.p) zeroTailA) σ +
            mpv (toTensorFromBlocks (d := blockPhysDim d familyA.p)
              (fun k => (μA k) ^ familyA.p)
              (fun k => blockTensor (d := d) (D := dimA k) (blocksA k) familyA.p)) σ) ∧
      (∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d familyB.p)),
        mpv (blockTensor (d := d) (D := D₂) B familyB.p) σ =
          mpv (zeroMPSTensor (blockPhysDim d familyB.p) zeroTailB) σ +
            mpv (toTensorFromBlocks (d := blockPhysDim d familyB.p)
              (fun k => (μB k) ^ familyB.p)
              (fun k => blockTensor (d := d) (D := dimB k) (blocksB k) familyB.p)) σ) ∧
      SameMPV₂
        (toTensorFromBlocks (d := blockPhysDim d familyA.p)
          (μ := fun k : Fin rA => (μA k) ^ familyA.p) familyA.commonReindexedBlock)
        (toTensorFromBlocks (d := blockPhysDim d familyA.p)
          (μ := familyA.commonFlatWeight μA) familyA.commonFlatBlocks) ∧
      SameMPV₂
        (toTensorFromBlocks (d := blockPhysDim d familyB.p)
          (μ := fun k : Fin rB => (μB k) ^ familyB.p) familyB.commonReindexedBlock)
        (toTensorFromBlocks (d := blockPhysDim d familyB.p)
          (μ := familyB.commonFlatWeight μB) familyB.commonFlatBlocks) ∧
      (∀ x, familyA.commonFlatWeight μA x ≠ 0) ∧
      (∀ x, familyB.commonFlatWeight μB x ≠ 0) ∧
      (∀ x, ∑ i : Fin (blockPhysDim d familyA.p),
        (familyA.commonFlatBlocks x i)ᴴ * familyA.commonFlatBlocks x i = 1) ∧
      (∀ x, ∑ i : Fin (blockPhysDim d familyB.p),
        (familyB.commonFlatBlocks x i)ᴴ * familyB.commonFlatBlocks x i = 1) ∧
      (∀ x, _root_.IsPrimitive
        (transferMap (d := blockPhysDim d familyA.p) (D := familyA.commonFlatDim x)
          (familyA.commonFlatBlocks x))) ∧
      (∀ x, _root_.IsPrimitive
        (transferMap (d := blockPhysDim d familyB.p) (D := familyB.commonFlatDim x)
          (familyB.commonFlatBlocks x))) ∧
      (∀ x, IsIrreducibleTensor (familyA.commonFlatBlocks x)) ∧
      (∀ x, IsIrreducibleTensor (familyB.commonFlatBlocks x)) ∧
      (∀ x, 0 < familyA.commonFlatDim x) ∧
      (∀ x, 0 < familyB.commonFlatDim x) := by
  obtain ⟨zeroTailA, rA, dimA, μA, blocksA,
      zeroTailB, rB, dimB, μB, blocksB,
      familyA, familyB, _hIrrA, _hIrrB, _hTPA, _hTPB, hμA, hμB, _hDimA, _hDimB,
      hMPVA, hMPVB, _hPos, _hZero, _hUnitA, _hUnitB⟩ :=
    afterBlocking_commonBlockedCyclicDataWithZeroTail_of_sameMPV₂ A B hSame
  refine ⟨zeroTailA, rA, dimA, μA, blocksA,
    zeroTailB, rB, dimB, μB, blocksB, familyA, familyB, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact zeroTail_toTensorFromBlocks_blockPower
      (d := d) (D := D₁) (r := rA) (z := zeroTailA) (p := familyA.p) (dim := dimA)
      A μA blocksA familyA.p_pos hMPVA
  · exact zeroTail_toTensorFromBlocks_blockPower
      (d := d) (D := D₂) (r := rB) (z := zeroTailB) (p := familyB.p) (dim := dimB)
      B μB blocksB familyB.p_pos hMPVB
  · exact familyA.sameMPV₂_weightedCommonReindexedBlock_commonFlat μA
  · exact familyB.sameMPV₂_weightedCommonReindexedBlock_commonFlat μB
  · intro x
    exact familyA.commonFlatWeight_ne_zero μA hμA x
  · intro x
    exact familyB.commonFlatWeight_ne_zero μB hμB x
  · intro x
    exact familyA.commonFlatBlocks_tp x
  · intro x
    exact familyB.commonFlatBlocks_tp x
  · intro x
    exact familyA.commonFlatBlocks_primitive x
  · intro x
    exact familyB.commonFlatBlocks_primitive x
  · intro x
    exact familyA.commonFlatBlocks_irreducible x
  · intro x
    exact familyB.commonFlatBlocks_irreducible x
  · intro x
    exact familyA.commonFlatDim_pos x
  · intro x
    exact familyB.commonFlatDim_pos x

set_option maxHeartbeats 800000 in
-- The next theorem has a large dependent existential conclusion, matching the
-- paper data used by the later sector comparison.

/-- **Two-sided common-length relabeled cyclic-sector theorem.**

Starting from `SameMPV₂ A B`, this theorem chooses one positive physical blocking
length for both sides.  At that common length it gives the exact zero-tail
identity for the canonically blocked nonzero parts, the positive-length equality
of those nonzero parts, and the relabeled cyclic-sector families produced by
`CommonBlockedCyclicSectorFamily` on both sides.

The last two `SameMPV₂` conclusions are deliberately stated for the relabeled
blocked sector blocks.  They isolate the remaining equality under the chosen word
reindexing needed to replace the canonical blocked nonzero blocks in the zero-tail
equations by the derived primitive irreducible common-sector blocks. -/
theorem afterBlocking_commonLengthCommonSectorData_of_sameMPV₂
    {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B) :
    ∃ (p : ℕ), 0 < p ∧
    ∃ (zeroTailA : ℕ) (rA : ℕ) (dimA : Fin rA → ℕ) (μA : Fin rA → ℂ)
      (blocksA : (k : Fin rA) → MPSTensor d (dimA k)),
    ∃ (zeroTailB : ℕ) (rB : ℕ) (dimB : Fin rB → ℕ) (μB : Fin rB → ℂ)
      (blocksB : (k : Fin rB) → MPSTensor d (dimB k)),
    ∃ (familyA : CommonBlockedCyclicSectorFamily blocksA),
    ∃ (familyB : CommonBlockedCyclicSectorFamily blocksB),
      familyA.p = p ∧
      familyB.p = p ∧
      (∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d p)),
        mpv (blockTensor (d := d) (D := D₁) A p) σ =
          mpv (zeroMPSTensor (blockPhysDim d p) zeroTailA) σ +
            mpv (toTensorFromBlocks (d := blockPhysDim d p)
              (fun k => (μA k) ^ p)
              (fun k => blockTensor (d := d) (D := dimA k) (blocksA k) p)) σ) ∧
      (∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d p)),
        mpv (blockTensor (d := d) (D := D₂) B p) σ =
          mpv (zeroMPSTensor (blockPhysDim d p) zeroTailB) σ +
            mpv (toTensorFromBlocks (d := blockPhysDim d p)
              (fun k => (μB k) ^ p)
              (fun k => blockTensor (d := d) (D := dimB k) (blocksB k) p)) σ) ∧
      SameMPV₂Pos
        (toTensorFromBlocks (d := blockPhysDim d p)
          (fun k => (μA k) ^ p)
          (fun k => blockTensor (d := d) (D := dimA k) (blocksA k) p))
        (toTensorFromBlocks (d := blockPhysDim d p)
          (fun k => (μB k) ^ p)
          (fun k => blockTensor (d := d) (D := dimB k) (blocksB k) p)) ∧
      (∀ σ : Fin 0 → Fin (blockPhysDim d p),
        (zeroTailA : ℂ) + mpv (toTensorFromBlocks (d := blockPhysDim d p)
          (fun k => (μA k) ^ p)
          (fun k => blockTensor (d := d) (D := dimA k) (blocksA k) p)) σ =
        (zeroTailB : ℂ) + mpv (toTensorFromBlocks (d := blockPhysDim d p)
          (fun k => (μB k) ^ p)
          (fun k => blockTensor (d := d) (D := dimB k) (blocksB k) p)) σ) ∧
      SameMPV₂
        (toTensorFromBlocks (d := blockPhysDim d familyA.p)
          (μ := fun k : Fin rA => (μA k) ^ familyA.p) familyA.commonReindexedBlock)
        (toTensorFromBlocks (d := blockPhysDim d familyA.p)
          (μ := familyA.commonFlatWeight μA) familyA.commonFlatBlocks) ∧
      SameMPV₂
        (toTensorFromBlocks (d := blockPhysDim d familyB.p)
          (μ := fun k : Fin rB => (μB k) ^ familyB.p) familyB.commonReindexedBlock)
        (toTensorFromBlocks (d := blockPhysDim d familyB.p)
          (μ := familyB.commonFlatWeight μB) familyB.commonFlatBlocks) ∧
      (∀ x, familyA.commonFlatWeight μA x ≠ 0) ∧
      (∀ x, familyB.commonFlatWeight μB x ≠ 0) ∧
      (∀ x, ∑ i : Fin (blockPhysDim d familyA.p),
        (familyA.commonFlatBlocks x i)ᴴ * familyA.commonFlatBlocks x i = 1) ∧
      (∀ x, ∑ i : Fin (blockPhysDim d familyB.p),
        (familyB.commonFlatBlocks x i)ᴴ * familyB.commonFlatBlocks x i = 1) ∧
      (∀ x, _root_.IsPrimitive
        (transferMap (d := blockPhysDim d familyA.p) (D := familyA.commonFlatDim x)
          (familyA.commonFlatBlocks x))) ∧
      (∀ x, _root_.IsPrimitive
        (transferMap (d := blockPhysDim d familyB.p) (D := familyB.commonFlatDim x)
          (familyB.commonFlatBlocks x))) ∧
      (∀ x, IsIrreducibleTensor (familyA.commonFlatBlocks x)) ∧
      (∀ x, IsIrreducibleTensor (familyB.commonFlatBlocks x)) ∧
      (∀ x, 0 < familyA.commonFlatDim x) ∧
      (∀ x, 0 < familyB.commonFlatDim x) := by
  obtain ⟨zeroTailA, rA, dimA, μA, blocksA,
      zeroTailB, rB, dimB, μB, blocksB,
      _hIrrA, _hIrrB, _hTPA, _hTPB, hμA, hμB, _hDimA, _hDimB,
      hMPVA, hMPVB, _hPos, _hZero, hCycA, hCycB⟩ :=
    afterBlocking_perBlockCyclicDataWithZeroTail_of_sameMPV₂ A B hSame
  let periodA : Fin rA → ℕ := fun k => (hCycA k).choose
  let periodB : Fin rB → ℕ := fun k => (hCycB k).choose
  have periodA_pos : ∀ k, 0 < periodA k := fun k => (hCycA k).choose_spec.1
  have periodB_pos : ∀ k, 0 < periodB k := fun k => (hCycB k).choose_spec.1
  let pA : ℕ := lcmPeriod periodA
  let pB : ℕ := lcmPeriod periodB
  let p : ℕ := Nat.lcm pA pB
  have hpA : 0 < pA := lcmPeriod_pos periodA_pos
  have hpB : 0 < pB := lcmPeriod_pos periodB_pos
  have hp : 0 < p := Nat.lcm_pos hpA hpB
  have hDvdA : ∀ k, (hCycA k).choose ∣ p := by
    intro k
    have h₁ : periodA k ∣ pA := dvd_lcmPeriod periodA k
    have h₂ : periodA k ∣ p := by
      exact Nat.dvd_trans h₁ (Nat.dvd_lcm_left pA pB)
    simpa [periodA] using h₂
  have hDvdB : ∀ k, (hCycB k).choose ∣ p := by
    intro k
    have h₁ : periodB k ∣ pB := dvd_lcmPeriod periodB k
    have h₂ : periodB k ∣ p := by
      exact Nat.dvd_trans h₁ (Nat.dvd_lcm_right pA pB)
    simpa [periodB] using h₂
  obtain ⟨⟨familyA, hFamilyA⟩⟩ :=
    exists_commonBlockedCyclicSectorFamily_of_commonMultiple
      blocksA hCycA p hp hDvdA
  obtain ⟨⟨familyB, hFamilyB⟩⟩ :=
    exists_commonBlockedCyclicSectorFamily_of_commonMultiple
      blocksB hCycB p hp hDvdB
  have hZA := zeroTail_toTensorFromBlocks_blockPower
    (d := d) (D := D₁) (r := rA) (z := zeroTailA) (p := p) (dim := dimA)
    A μA blocksA hp hMPVA
  have hZB := zeroTail_toTensorFromBlocks_blockPower
    (d := d) (D := D₂) (r := rB) (z := zeroTailB) (p := p) (dim := dimB)
    B μB blocksB hp hMPVB
  have hBook :=
    nonzeroBlock_blockPower_positive_sameMPV₂_and_zeroTail_identity_of_sameMPV₂
      A B hSame zeroTailA zeroTailB μA blocksA μB blocksB hp hMPVA hMPVB
  refine ⟨p, hp, zeroTailA, rA, dimA, μA, blocksA,
    zeroTailB, rB, dimB, μB, blocksB, familyA, familyB,
    hFamilyA, hFamilyB, hZA, hZB, hBook.1, hBook.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · exact familyA.sameMPV₂_weightedCommonReindexedBlock_commonFlat μA
  · exact familyB.sameMPV₂_weightedCommonReindexedBlock_commonFlat μB
  · intro x
    exact familyA.commonFlatWeight_ne_zero μA hμA x
  · intro x
    exact familyB.commonFlatWeight_ne_zero μB hμB x
  · intro x
    exact familyA.commonFlatBlocks_tp x
  · intro x
    exact familyB.commonFlatBlocks_tp x
  · intro x
    exact familyA.commonFlatBlocks_primitive x
  · intro x
    exact familyB.commonFlatBlocks_primitive x
  · intro x
    exact familyA.commonFlatBlocks_irreducible x
  · intro x
    exact familyB.commonFlatBlocks_irreducible x
  · intro x
    exact familyA.commonFlatDim_pos x
  · intro x
    exact familyB.commonFlatDim_pos x

set_option maxHeartbeats 900000 in
-- The nested existential conclusion records both sides and the conditional
-- common-sector equalities.
/-- **Common-length cyclic sectors after reindexing blocked words.**

This theorem records the common-length data in the form used by the later
sector comparison.  It first chooses one blocking length for both tensors and
records the common cyclic-sector families.  If the canonical blocked nonzero
families agree with the explicitly reindexed blocked-word families, then the
nonzero parts are equal to the weighted common-sector families, and the zero-tail
equations are rewritten with those common-sector families. -/
theorem afterBlocking_commonLengthCommonSectorData_of_reindexed
    {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B) :
    ∃ (p : ℕ), 0 < p ∧
    ∃ (zeroTailA : ℕ) (rA : ℕ) (dimA : Fin rA → ℕ) (μA : Fin rA → ℂ)
      (blocksA : (k : Fin rA) → MPSTensor d (dimA k)),
    ∃ (zeroTailB : ℕ) (rB : ℕ) (dimB : Fin rB → ℕ) (μB : Fin rB → ℂ)
      (blocksB : (k : Fin rB) → MPSTensor d (dimB k)),
    ∃ (familyA : CommonBlockedCyclicSectorFamily blocksA),
    ∃ (familyB : CommonBlockedCyclicSectorFamily blocksB),
    ∃ (hFamilyA : familyA.p = p), ∃ (hFamilyB : familyB.p = p),
      (∀ x, familyA.commonFlatWeight μA x ≠ 0) ∧
      (∀ x, familyB.commonFlatWeight μB x ≠ 0) ∧
      (∀ x, ∑ i : Fin (blockPhysDim d familyA.p),
        (familyA.commonFlatBlocks x i)ᴴ * familyA.commonFlatBlocks x i = 1) ∧
      (∀ x, ∑ i : Fin (blockPhysDim d familyB.p),
        (familyB.commonFlatBlocks x i)ᴴ * familyB.commonFlatBlocks x i = 1) ∧
      (∀ x, _root_.IsPrimitive
        (transferMap (d := blockPhysDim d familyA.p) (D := familyA.commonFlatDim x)
          (familyA.commonFlatBlocks x))) ∧
      (∀ x, _root_.IsPrimitive
        (transferMap (d := blockPhysDim d familyB.p) (D := familyB.commonFlatDim x)
          (familyB.commonFlatBlocks x))) ∧
      (∀ x, IsIrreducibleTensor (familyA.commonFlatBlocks x)) ∧
      (∀ x, IsIrreducibleTensor (familyB.commonFlatBlocks x)) ∧
      (∀ x, 0 < familyA.commonFlatDim x) ∧
      (∀ x, 0 < familyB.commonFlatDim x) ∧
      (SameMPV₂
        (toTensorFromBlocks (d := blockPhysDim d familyA.p)
          (μ := fun k : Fin rA => (μA k) ^ familyA.p)
          (fun k => blockTensor (d := d) (D := dimA k) (blocksA k) familyA.p))
        (toTensorFromBlocks (d := blockPhysDim d familyA.p)
          (μ := fun k : Fin rA => (μA k) ^ familyA.p) familyA.commonReindexedBlock) →
      SameMPV₂
        (toTensorFromBlocks (d := blockPhysDim d familyB.p)
          (μ := fun k : Fin rB => (μB k) ^ familyB.p)
          (fun k => blockTensor (d := d) (D := dimB k) (blocksB k) familyB.p))
        (toTensorFromBlocks (d := blockPhysDim d familyB.p)
          (μ := fun k : Fin rB => (μB k) ^ familyB.p) familyB.commonReindexedBlock) →
        SameMPV₂
          (toTensorFromBlocks (d := blockPhysDim d p)
            (μ := fun k : Fin rA => (μA k) ^ p)
            (fun k => blockTensor (d := d) (D := dimA k) (blocksA k) p))
          (toTensorFromBlocks (d := blockPhysDim d p)
            (μ := familyA.commonFlatWeight μA) (familyA.commonFlatBlocksAt hFamilyA)) ∧
        SameMPV₂
          (toTensorFromBlocks (d := blockPhysDim d p)
            (μ := fun k : Fin rB => (μB k) ^ p)
            (fun k => blockTensor (d := d) (D := dimB k) (blocksB k) p))
          (toTensorFromBlocks (d := blockPhysDim d p)
            (μ := familyB.commonFlatWeight μB) (familyB.commonFlatBlocksAt hFamilyB)) ∧
        (∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d p)),
          mpv (blockTensor (d := d) (D := D₁) A p) σ =
            mpv (zeroMPSTensor (blockPhysDim d p) zeroTailA) σ +
              mpv (toTensorFromBlocks (d := blockPhysDim d p)
                (μ := familyA.commonFlatWeight μA) (familyA.commonFlatBlocksAt hFamilyA)) σ) ∧
        (∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d p)),
          mpv (blockTensor (d := d) (D := D₂) B p) σ =
            mpv (zeroMPSTensor (blockPhysDim d p) zeroTailB) σ +
              mpv (toTensorFromBlocks (d := blockPhysDim d p)
                (μ := familyB.commonFlatWeight μB) (familyB.commonFlatBlocksAt hFamilyB)) σ) ∧
        SameMPV₂Pos
          (blockTensor (d := d) (D := D₁) A p)
          (toTensorFromBlocks (d := blockPhysDim d p)
            (μ := familyA.commonFlatWeight μA) (familyA.commonFlatBlocksAt hFamilyA)) ∧
        SameMPV₂Pos
          (blockTensor (d := d) (D := D₂) B p)
          (toTensorFromBlocks (d := blockPhysDim d p)
            (μ := familyB.commonFlatWeight μB) (familyB.commonFlatBlocksAt hFamilyB)) ∧
        SameMPV₂Pos
          (toTensorFromBlocks (d := blockPhysDim d p)
            (μ := familyA.commonFlatWeight μA) (familyA.commonFlatBlocksAt hFamilyA))
          (toTensorFromBlocks (d := blockPhysDim d p)
            (μ := familyB.commonFlatWeight μB) (familyB.commonFlatBlocksAt hFamilyB)) ∧
        (∀ σ : Fin 0 → Fin (blockPhysDim d p),
          (zeroTailA : ℂ) + mpv (toTensorFromBlocks (d := blockPhysDim d p)
            (μ := familyA.commonFlatWeight μA) (familyA.commonFlatBlocksAt hFamilyA)) σ =
          (zeroTailB : ℂ) + mpv (toTensorFromBlocks (d := blockPhysDim d p)
            (μ := familyB.commonFlatWeight μB) (familyB.commonFlatBlocksAt hFamilyB)) σ)) := by
  obtain ⟨p, hp, zeroTailA, rA, dimA, μA, blocksA,
      zeroTailB, rB, dimB, μB, blocksB, familyA, familyB,
      hFamilyA, hFamilyB, hZA, hZB, hPos, hZero,
      _hReindexA, _hReindexB, hμA, hμB, hTPA, hTPB, hPrimA, hPrimB,
      hIrrA, hIrrB, hDimA, hDimB⟩ :=
    afterBlocking_commonLengthCommonSectorData_of_sameMPV₂ A B hSame
  refine ⟨p, hp, zeroTailA, rA, dimA, μA, blocksA,
    zeroTailB, rB, dimB, μB, blocksB, familyA, familyB, hFamilyA, hFamilyB,
    hμA, hμB, hTPA, hTPB, hPrimA, hPrimB, hIrrA, hIrrB, hDimA, hDimB, ?_⟩
  intro hRelabelA hRelabelB
  have hFlatA := familyA.sameMPV₂_weightedCanonicalBlock_commonFlatAt_of_reindexed
    μA hFamilyA hRelabelA
  have hFlatB := familyB.sameMPV₂_weightedCanonicalBlock_commonFlatAt_of_reindexed
    μB hFamilyB hRelabelB
  have hZAflat : ∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d p)),
      mpv (blockTensor (d := d) (D := D₁) A p) σ =
        mpv (zeroMPSTensor (blockPhysDim d p) zeroTailA) σ +
          mpv (toTensorFromBlocks (d := blockPhysDim d p)
            (μ := familyA.commonFlatWeight μA) (familyA.commonFlatBlocksAt hFamilyA)) σ :=
    zeroTail_eq_of_sameMPV₂ _ _ _ hZA hFlatA
  have hZBflat : ∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d p)),
      mpv (blockTensor (d := d) (D := D₂) B p) σ =
        mpv (zeroMPSTensor (blockPhysDim d p) zeroTailB) σ +
          mpv (toTensorFromBlocks (d := blockPhysDim d p)
            (μ := familyB.commonFlatWeight μB) (familyB.commonFlatBlocksAt hFamilyB)) σ :=
    zeroTail_eq_of_sameMPV₂ _ _ _ hZB hFlatB
  have hApos : SameMPV₂Pos (blockTensor (d := d) (D := D₁) A p)
      (toTensorFromBlocks (d := blockPhysDim d p)
        (μ := familyA.commonFlatWeight μA) (familyA.commonFlatBlocksAt hFamilyA)) :=
    sameMPV₂Pos_of_zeroTail_eq _ _ hZAflat
  have hBpos : SameMPV₂Pos (blockTensor (d := d) (D := D₂) B p)
      (toTensorFromBlocks (d := blockPhysDim d p)
        (μ := familyB.commonFlatWeight μB) (familyB.commonFlatBlocksAt hFamilyB)) :=
    sameMPV₂Pos_of_zeroTail_eq _ _ hZBflat
  have hFlatPos : SameMPV₂Pos
      (toTensorFromBlocks (d := blockPhysDim d p)
        (μ := familyA.commonFlatWeight μA) (familyA.commonFlatBlocksAt hFamilyA))
      (toTensorFromBlocks (d := blockPhysDim d p)
        (μ := familyB.commonFlatWeight μB) (familyB.commonFlatBlocksAt hFamilyB)) := by
    intro N hN σ
    calc
      mpv (toTensorFromBlocks (d := blockPhysDim d p)
          (μ := familyA.commonFlatWeight μA) (familyA.commonFlatBlocksAt hFamilyA)) σ =
          mpv (toTensorFromBlocks (d := blockPhysDim d p)
            (fun k => (μA k) ^ p)
            (fun k => blockTensor (d := d) (D := dimA k) (blocksA k) p)) σ :=
            (hFlatA N σ).symm
      _ = mpv (toTensorFromBlocks (d := blockPhysDim d p)
            (fun k => (μB k) ^ p)
            (fun k => blockTensor (d := d) (D := dimB k) (blocksB k) p)) σ :=
            hPos N hN σ
      _ = mpv (toTensorFromBlocks (d := blockPhysDim d p)
          (μ := familyB.commonFlatWeight μB) (familyB.commonFlatBlocksAt hFamilyB)) σ :=
            hFlatB N σ
  have hZeroFlat : ∀ σ : Fin 0 → Fin (blockPhysDim d p),
      (zeroTailA : ℂ) + mpv (toTensorFromBlocks (d := blockPhysDim d p)
        (μ := familyA.commonFlatWeight μA) (familyA.commonFlatBlocksAt hFamilyA)) σ =
      (zeroTailB : ℂ) + mpv (toTensorFromBlocks (d := blockPhysDim d p)
        (μ := familyB.commonFlatWeight μB) (familyB.commonFlatBlocksAt hFamilyB)) σ := by
    intro σ
    calc
      (zeroTailA : ℂ) + mpv (toTensorFromBlocks (d := blockPhysDim d p)
          (μ := familyA.commonFlatWeight μA) (familyA.commonFlatBlocksAt hFamilyA)) σ =
          (zeroTailA : ℂ) + mpv (toTensorFromBlocks (d := blockPhysDim d p)
            (fun k => (μA k) ^ p)
            (fun k => blockTensor (d := d) (D := dimA k) (blocksA k) p)) σ := by
            rw [(hFlatA 0 σ).symm]
      _ = (zeroTailB : ℂ) + mpv (toTensorFromBlocks (d := blockPhysDim d p)
            (fun k => (μB k) ^ p)
            (fun k => blockTensor (d := d) (D := dimB k) (blocksB k) p)) σ := hZero σ
      _ = (zeroTailB : ℂ) + mpv (toTensorFromBlocks (d := blockPhysDim d p)
          (μ := familyB.commonFlatWeight μB) (familyB.commonFlatBlocksAt hFamilyB)) σ := by
            rw [hFlatB 0 σ]
  exact ⟨hFlatA, hFlatB, hZAflat, hZBflat, hApos, hBpos, hFlatPos, hZeroFlat⟩

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

/-!
### What remains for the full 1606.00608 Fundamental Theorem

The complete fundamental theorem should take two tensors `A, B` with `SameMPV₂ A B`
and pass from the blocked reduction data to the paper's basis-of-normal-tensors
sector comparison. The one-sided phase-class BNT construction is available as
`exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks`, with one-sided overlap data
exposed by `exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks_with_overlapOrtho`.
The sector matching extraction is available from primitive overlap-rigidity
hypotheses through `SectorBasisOverlapSpanHypotheses.exists_sectorBasisMatching`.

The theorem
`fundamentalTheorem_after_blocking_sector_of_common_blocks_injectiveSpan`
gives a nonzero-part overlap-span reduction from span equality for the
constructed sector bases. The theorem
`fundamentalTheorem_after_blocking_sector_of_common_blocks_blockSpan`
strengthens this in the phase-class representative setting: equality of the
finite-length spans of the original nonzero-weight block families is transported to the
chosen sector bases and the sector-weight conclusion follows from the original
`SameMPV₂ A B`. The theorem
`fundamentalTheorem_after_blocking_sector_of_common_blocks_overlapSpan_zeroTail`
gives the corresponding zero-tail route when full overlap-span data
are supplied.

The blocked-word relabelling and common primitive irreducible nonzero-block
decompositions are now part of this file's structural reduction. The remaining
formal work for the completely unconditional
`fundamentalTheorem_after_blocking_sector` is therefore narrower:

1. the `N = 0` identity for the zero-tail contribution;
2. one-site injectivity of the nonzero-weight blocks, or a blocked replacement of the
   rigidity hypothesis; and
3. equality of the finite-length MPV spans for the original nonzero-weight block families
   (or directly for the two BNT bases), equivalently a common phase/BNT-cover comparison,
   followed by the final global gauge construction of the equal-case FT.

Thus the common-period arithmetic, the blocked-word relabelling, the common
primitive irreducible nonzero-sector families, and the abstract sector-matching
witness are no longer the main blockers. The remaining gap is the paper-level
derivation of the listed zero-tail, injectivity, and span/comparison facts for
the actual sector tensors produced by the after-blocking reduction.
-/

end FundamentalTheoremAfterBlocking

end MPSTensor

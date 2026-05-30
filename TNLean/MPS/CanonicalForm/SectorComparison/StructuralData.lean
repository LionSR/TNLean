/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.SectorComparison.CommonSectorData

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
* `afterBlocking_tpPrimitiveBlockDecompositions_of_sameMPV₂` — two tensors with
  the same matrix-product-vector family have, after separate positive blockings,
  trace-preserving primitive block decompositions on both sides; each blocked
  tensor equals its nonzero-weight block sum at every positive length.

## References

* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608, Section 2.3 + Appendix A]
* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:2011.12127, Section IV]

## Tags

matrix product states, canonical form, common period, after-blocking reduction
-/

namespace MPSTensor

variable {d D : ℕ}

/-!
## Canonical-form reduction after blocking

### Overview

After blocking, the canonical-form reduction writes an MPS tensor as an
all-zero summand together with a weighted direct sum of nonzero sectors:
`blockTensor A p ~ zeroMPSTensor d D₀ + toTensorFromBlocks μ sectors`, with
`p > 0`.  This is the formal counterpart of the CPSV allowance
`∑ k, D_k ≤ D`, where zero blocks may occur.

The full proof chain is:
1. Zero-block separation (`exists_irreducible_blockDecomp_nonzeroBlocks`)
2. TP gauge (`exists_tp_gauge_from_arbitrary_with_zeroTail`)
3. Common blocking to primitive (`exists_common_blocking_all_primitive_of_TP_irr`)
4. Cyclic sector decomposition per block (`exists_cyclic_sector_decomp_after_blocking`)

### Remaining mathematical assumptions

The after-blocking primitive block decomposition provides:
- A blocking period `p > 0`
- A trivial all-zero block of dimension `zeroTailDim`, representing the CPSV
  allowance `∑ k, D_k ≤ D` where zero blocks may occur
- A family of TP sector blocks
- The MPV relationship: `blockTensor A p` is `SameMPV₂`-equivalent to
  `zeroMPSTensor + toTensorFromBlocks μ sectors` for some weights `μ`

The current library already settles the common-period blocking arithmetic and
now has a one-sided phase-class BNT construction for TP primitive irreducible
nonzero-weight blocks, one-sided overlap data, and zero-tail sector comparison
from finite-length span or BNT comparison hypotheses. The theorem
`afterBlocking_perBlockCyclicDataWithZeroTail_of_sameMPV₂`
follows the CPSV order: first separate the all-zero leftover block and
TP-gauge the irreducible nonzero-weight blocks, then remove each block's period by
cyclic sectors.
It deliberately does not identify that period-removal length with the later
finite blocking length used for common refinement or injectivity.

The comparison data separated here are zero-block cancellation, finite-length
span equality, and BNT sector matching.

The common-sector theorem then rewrites the cyclic sectors at one common
physical blocking length.  The remaining assumptions are one-site injectivity
(or a blocked replacement), finite-length span equality at that length, and
the length-zero identity for the all-zero leftover block.
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

/-- **Structural after-blocking theorem at positive lengths.**

After separate positive blockings, two tensors with the same matrix-product-vector
family each split into trace-preserving nonzero-weight blocks with primitive
transfer maps, positive bond dimensions, and nonzero weights. The two original
tensors still have the same matrix-product-vector family at both chosen
blocking lengths, and each blocked tensor agrees with its nonzero-weight block
sum at every positive length. The all-zero leftover block contributes only at
length zero, so it is omitted: the positive-length equality is the only content
needed for the later sector comparison, and the length-zero coefficient is
restored once, at the end, from equality of the bond dimensions. -/
theorem afterBlocking_tpPrimitiveBlockDecompositions_of_sameMPV₂
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
      (∀ k, 0 < dimB k) ∧
      SameMPV₂Pos (blockTensor (d := d) (D := D₁) A pA)
        (toTensorFromBlocks (d := blockPhysDim d pA) (μ := μA) blocksA) ∧
      SameMPV₂Pos (blockTensor (d := d) (D := D₂) B pB)
        (toTensorFromBlocks (d := blockPhysDim d pB) (μ := μB) blocksB) := by
  obtain ⟨zeroTailA, pA, hpA, rA, dimA, μA, blocksA, hTPA, hPrimA, hDimA, hμA, hMPVA⟩ :=
    exists_tp_primitive_blockDecomp_after_blocking A
  obtain ⟨zeroTailB, pB, hpB, rB, dimB, μB, blocksB, hTPB, hPrimB, hDimB, hμB, hMPVB⟩ :=
    exists_tp_primitive_blockDecomp_after_blocking B
  refine ⟨pA, hpA, rA, dimA, μA, blocksA,
    pB, hpB, rB, dimB, μB, blocksB,
    ?_, ?_, hTPA, hTPB, hPrimA, hPrimB, hμA, hμB, hDimA, hDimB, ?_, ?_⟩
  · exact sameMPV₂_blockTensor A B hSame pA
  · exact sameMPV₂_blockTensor A B hSame pB
  · exact sameMPV₂Pos_of_zeroTail_eq _ _ hMPVA
  · exact sameMPV₂Pos_of_zeroTail_eq _ _ hMPVB


end FundamentalTheoremAfterBlocking

end MPSTensor

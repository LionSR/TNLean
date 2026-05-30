/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.SectorComparison.CommonBlockedCyclicSectorConstruction
import TNLean.MPS.CanonicalForm.SectorComparison.NonzeroBlockComparison
import TNLean.MPS.CanonicalForm.SectorComparison.ZeroTailTransport

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Filter

/-!
# Common-sector witnesses for the after-blocking reduction

This file collects the common-sector continuation of the structural
canonical-form reduction following arXiv:1606.00608. Starting from the
all-zero leftover block and TP-gauge decomposition, it records the per-block
weights, blocks, and positive-length agreements of the nonzero part, chooses
common blocking lengths, and states the relabeled common-sector families needed
to compare the resulting sector families.

## Main statements

* `afterBlocking_perBlockCyclicData_of_sameMPV₂` — per-block weights, blocks,
  cyclic-sector decompositions, and positive-length nonzero-sector identities.
* `afterBlocking_commonLengthCommonSectorData_of_sameMPV₂` — a two-sided
  common blocking length with common-sector families.

## References

* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608, Section 2.3 + Appendix A]
* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:2011.12127, Section IV]

## Tags

matrix product states, canonical form, common sectors, blocking
-/

namespace MPSTensor

variable {d D : ℕ}

section FundamentalTheoremAfterBlocking

/-- **Per-block cyclic-sector decomposition after the zero-block split.**

This is the faithful predecessor to the common nonzero-sector statement. From
`SameMPV₂ A B`, it first separates the all-zero leftover block and then applies
the TP gauge to obtain irreducible nonzero-weight blocks on both sides. It then
removes the period of each block separately, producing primitive irreducible cyclic sectors for
every nonzero-weight block. The tensor on each side agrees with its nonzero part
at every positive length, and the two nonzero parts agree at every positive length.
The length-zero coefficient is recovered separately, at the end, from equality of
the bond dimensions.

The theorem intentionally keeps the per-block period-removal lengths inside
`HasPrimitiveIrreducibleCyclicSectors`. It does not conflate those lengths with a
later common-refinement or Wielandt/injectivity blocking length; assembling the
per-block cyclic sectors at one physical blocking level is the next formal
statement in the reduction chain. -/
theorem afterBlocking_perBlockCyclicData_of_sameMPV₂
    {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B) :
    ∃ (rA : ℕ) (dimA : Fin rA → ℕ) (μA : Fin rA → ℂ)
      (blocksA : (k : Fin rA) → MPSTensor d (dimA k)),
    ∃ (rB : ℕ) (dimB : Fin rB → ℕ) (μB : Fin rB → ℂ)
      (blocksB : (k : Fin rB) → MPSTensor d (dimB k)),
      (∀ k, IsIrreducibleTensor (blocksA k)) ∧
      (∀ k, IsIrreducibleTensor (blocksB k)) ∧
      (∀ k, ∑ i : Fin d, (blocksA k i)ᴴ * blocksA k i = 1) ∧
      (∀ k, ∑ i : Fin d, (blocksB k i)ᴴ * blocksB k i = 1) ∧
      (∀ k, μA k ≠ 0) ∧
      (∀ k, μB k ≠ 0) ∧
      (∀ k, 0 < dimA k) ∧
      (∀ k, 0 < dimB k) ∧
      SameMPV₂Pos A (toTensorFromBlocks (d := d) (μ := μA) blocksA) ∧
      SameMPV₂Pos B (toTensorFromBlocks (d := d) (μ := μB) blocksB) ∧
      SameMPV₂Pos
        (toTensorFromBlocks (d := d) (μ := μA) blocksA)
        (toTensorFromBlocks (d := d) (μ := μB) blocksB) ∧
      (∀ k, HasPrimitiveIrreducibleCyclicSectors (blocksA k)) ∧
      (∀ k, HasPrimitiveIrreducibleCyclicSectors (blocksB k)) := by
  obtain ⟨zeroTailA, rA, dimA, μA, blocksA,
      hIrrA, hTPA, hμA, hDimA, hMPVA⟩ :=
    exists_tp_gauge_from_arbitrary_with_zeroTail (d := d) (D := D₁) A
  obtain ⟨zeroTailB, rB, dimB, μB, blocksB,
      hIrrB, hTPB, hμB, hDimB, hMPVB⟩ :=
    exists_tp_gauge_from_arbitrary_with_zeroTail (d := d) (D := D₂) B
  have hBook :=
    nonzeroBlock_sameMPV₂Pos_of_sameMPV₂
      A B hSame zeroTailA zeroTailB μA blocksA μB blocksB hMPVA hMPVB
  have hAPos := sameMPV₂Pos_of_zeroTail_eq A
    (toTensorFromBlocks (d := d) (μ := μA) blocksA) hMPVA
  have hBPos := sameMPV₂Pos_of_zeroTail_eq B
    (toTensorFromBlocks (d := d) (μ := μB) blocksB) hMPVB
  refine ⟨rA, dimA, μA, blocksA, rB, dimB, μB, blocksB,
    hIrrA, hIrrB, hTPA, hTPB, hμA, hμB, hDimA, hDimB, hAPos, hBPos,
    hBook, ?_, ?_⟩
  · intro k
    letI : NeZero (dimA k) := ⟨Nat.ne_of_gt (hDimA k)⟩
    exact hasPrimitiveIrreducibleCyclicSectors_of_TP_of_isIrreducibleTensor
      (blocksA k) (hTPA k) (hIrrA k)
  · intro k
    letI : NeZero (dimB k) := ⟨Nat.ne_of_gt (hDimB k)⟩
    exact hasPrimitiveIrreducibleCyclicSectors_of_TP_of_isIrreducibleTensor
      (blocksB k) (hTPB k) (hIrrB k)

set_option maxHeartbeats 800000 in
-- The next theorem has a large dependent existential conclusion, matching the
-- CPSV witnesses used by the later sector comparison.

/-- **Two-sided common-length relabeled cyclic-sector theorem.**

Starting from `SameMPV₂ A B`, this theorem chooses one positive physical blocking
length for both sides.  At that common length it gives, for each side, the
positive-length equality between the blocked tensor and its weighted nonzero part,
the positive-length equality of the two nonzero parts, and the relabeled
cyclic-sector families produced by `CommonBlockedCyclicSectorFamily`.

The last two `SameMPV₂` conclusions are deliberately stated for the relabeled
blocked sector blocks.  They isolate the remaining equality under the chosen word
reindexing needed to replace the canonical blocked nonzero blocks by the derived
primitive irreducible common-sector blocks. -/
theorem afterBlocking_commonLengthCommonSectorData_of_sameMPV₂
    {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B) :
    ∃ (p : ℕ), 0 < p ∧
    ∃ (rA : ℕ) (dimA : Fin rA → ℕ) (μA : Fin rA → ℂ)
      (blocksA : (k : Fin rA) → MPSTensor d (dimA k)),
    ∃ (rB : ℕ) (dimB : Fin rB → ℕ) (μB : Fin rB → ℂ)
      (blocksB : (k : Fin rB) → MPSTensor d (dimB k)),
    ∃ (familyA : CommonBlockedCyclicSectorFamily blocksA),
    ∃ (familyB : CommonBlockedCyclicSectorFamily blocksB),
      familyA.p = p ∧
      familyB.p = p ∧
      SameMPV₂Pos
        (blockTensor (d := d) (D := D₁) A p)
        (toTensorFromBlocks (d := blockPhysDim d p)
          (fun k => (μA k) ^ p)
          (fun k => blockTensor (d := d) (D := dimA k) (blocksA k) p)) ∧
      SameMPV₂Pos
        (blockTensor (d := d) (D := D₂) B p)
        (toTensorFromBlocks (d := blockPhysDim d p)
          (fun k => (μB k) ^ p)
          (fun k => blockTensor (d := d) (D := dimB k) (blocksB k) p)) ∧
      SameMPV₂Pos
        (toTensorFromBlocks (d := blockPhysDim d p)
          (fun k => (μA k) ^ p)
          (fun k => blockTensor (d := d) (D := dimA k) (blocksA k) p))
        (toTensorFromBlocks (d := blockPhysDim d p)
          (fun k => (μB k) ^ p)
          (fun k => blockTensor (d := d) (D := dimB k) (blocksB k) p)) ∧
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
  obtain ⟨rA, dimA, μA, blocksA,
      rB, dimB, μB, blocksB,
      _hIrrA, _hIrrB, _hTPA, _hTPB, hμA, hμB, _hDimA, _hDimB,
      hAPos, hBPos, hPos, hCycA, hCycB⟩ :=
    afterBlocking_perBlockCyclicData_of_sameMPV₂ A B hSame
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
    have h₂ : periodA k ∣ p :=
      Nat.dvd_trans h₁ (Nat.dvd_lcm_left pA pB)
    simpa [periodA] using h₂
  have hDvdB : ∀ k, (hCycB k).choose ∣ p := by
    intro k
    have h₁ : periodB k ∣ pB := dvd_lcmPeriod periodB k
    have h₂ : periodB k ∣ p :=
      Nat.dvd_trans h₁ (Nat.dvd_lcm_right pA pB)
    simpa [periodB] using h₂
  obtain ⟨⟨familyA, hFamilyA⟩⟩ :=
    exists_commonBlockedCyclicSectorFamily_of_commonMultiple
      blocksA hCycA p hp hDvdA
  obtain ⟨⟨familyB, hFamilyB⟩⟩ :=
    exists_commonBlockedCyclicSectorFamily_of_commonMultiple
      blocksB hCycB p hp hDvdB
  have hAPosCanon :=
    sameMPV₂Pos_blockTensor_toTensorFromBlocks
      (d := d) A μA blocksA hAPos p hp
  have hBPosCanon :=
    sameMPV₂Pos_blockTensor_toTensorFromBlocks
      (d := d) B μB blocksB hBPos p hp
  have hBook :=
    sameMPV₂Pos_toTensorFromBlocks_blockPower
      (d := d) μA blocksA μB blocksB hPos p hp
  refine ⟨p, hp, rA, dimA, μA, blocksA,
    rB, dimB, μB, blocksB, familyA, familyB,
    hFamilyA, hFamilyB, hAPosCanon, hBPosCanon, hBook, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
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

/-!
### What remains for the full 1606.00608 Fundamental Theorem

The complete fundamental theorem should take two tensors `A, B` with `SameMPV₂ A B`
and pass from the blocked reduction witnesses to the CPSV basis-of-normal-tensors
sector comparison. The one-sided phase-class BNT construction is available as
`exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks`; the remaining overlap/span
hypotheses are supplied at the two-sided comparison layer.
The sector matching extraction is available from primitive overlap-rigidity
hypotheses through `SectorBasisOverlapSpanHypotheses.exists_sectorBasisMatching`.

The comparison hypotheses match the CPSV boundary: blocked-word relabeling,
finite-length nonzero-block span comparison, and BNT sector
matching.

The blocked-word relabeling and common primitive irreducible nonzero-block
decompositions are now part of this file's structural reduction. The remaining
formal work for the completely unconditional
`fundamentalTheorem_after_blocking_sector` is therefore narrower:

1. the `N = 0` identity for the zero-tail contribution;
2. one-site injectivity of the nonzero-weight blocks, or a blocked replacement of the
   rigidity hypothesis; and
3. equality of the finite-length MPV spans for the original nonzero-weight block families
   (or directly for the two BNT bases), equivalently a common phase/BNT comparison,
   followed by the final global gauge construction of the equal-case FT.

Thus the common-period arithmetic, the blocked-word relabeling, the common
primitive irreducible nonzero-sector families, and the abstract sector-matching
witness have already been supplied. What remains is the CPSV derivation of the
listed zero-tail, injectivity, and span/comparison facts for the actual sector
tensors produced by the after-blocking reduction.
-/

end FundamentalTheoremAfterBlocking

end MPSTensor

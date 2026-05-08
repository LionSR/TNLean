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
# Common-sector data for the after-blocking reduction

This file collects the common-sector continuation of the structural
canonical-form reduction following arXiv:1606.00608. Starting from the
all-zero leftover block and TP-gauge decomposition, it records the per-block
cyclic-sector data, chooses common blocking lengths, and states the relabeled
common-sector data needed to compare the resulting sector families.  The
`zeroTail` variables below name the total bond dimension of the all-zero blocks,
corresponding to the source-paper allowance `∑ k, D_k ≤ D`.

## Main statements

* `afterBlocking_perBlockCyclicDataWithZeroTail_of_sameMPV₂` — per-block
  cyclic-sector data together with the zero-tail identity.
* `afterBlocking_commonLengthCommonSectorData_of_sameMPV₂` — a two-sided
  common blocking length with common-sector families.
* `afterBlocking_commonLengthCommonSectorData_of_reindexed` — the same data
  after the blocked-word relabeling hypotheses used downstream.

## References

* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608, Section 2.3 + Appendix A]
* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:2011.12127, Section IV]

## Tags

matrix product states, canonical form, common sectors, blocking
-/

namespace MPSTensor

variable {d D : ℕ}

section FundamentalTheoremAfterBlocking

/-- **Per-block cyclic-sector decomposition with a zero-tail identity.**

This is the faithful predecessor to the common nonzero-sector statement. From
`SameMPV₂ A B`, it first separates the all-zero leftover block and then applies
the TP gauge to obtain irreducible nonzero-weight blocks on both sides. It then
removes the period of each block separately, producing primitive irreducible cyclic sectors for
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

/-!
### What remains for the full 1606.00608 Fundamental Theorem

The complete fundamental theorem should take two tensors `A, B` with `SameMPV₂ A B`
and pass from the blocked reduction data to the paper's basis-of-normal-tensors
sector comparison. The one-sided phase-class BNT construction is available as
`exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks`, with one-sided overlap data
exposed by `exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks_with_overlapOrtho`.
The sector matching extraction is available from primitive overlap-rigidity
hypotheses through `SectorBasisOverlapSpanHypotheses.exists_sectorBasisMatching`.

The current comparison uses
`afterBlocking_sectorComparison_zeroTail_of_blockSpan` and the common phase-cover
or BNT comparison theorems. This avoids keeping separate common-block comparison
variants as public waypoints: the formal residue is the paper-level residue,
namely blocked-word relabeling, finite-length nonzero-block span comparison,
and BNT sector matching.

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
witness are no longer the main blockers. The remaining gap is the paper-level
derivation of the listed zero-tail, injectivity, and span/comparison facts for
the actual sector tensors produced by the after-blocking reduction.
-/

end FundamentalTheoremAfterBlocking

end MPSTensor

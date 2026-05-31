/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.SectorComparison.StructuralData
import TNLean.MPS.CanonicalForm.SectorComparison.CommonBlockedCyclicSectorFamily

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Filter

namespace MPSTensor

/-!
# Common-sector transport after canonical-form blocking

This module contains the common-sector reindexing hypotheses used after the
structural canonical-form reduction has produced common cyclic-sector families.

## Main statements

* `CommonSectorRelabelingHypothesis` encodes the remaining blocked-word
  comparison hypothesis used by the conditional common-sector theorem.
* `afterBlocking_commonPrimitiveIrreducibleBlocks_of_reindexedNonzeroParts`
  and `unconditional_commonPrimitiveIrreducibleBlocks` turn the structural
  common-sector families into common primitive irreducible block decompositions.

## References

* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608, Section 2.3 + Appendix A]
* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:2011.12127, Section IV]

## Tags

matrix product states, canonical form, common sectors
-/

/-- The one-sided blocked-word relabeling hypothesis for cyclic-sector families.

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

set_option maxHeartbeats 800000 in
-- The conclusion records both decompositions and all their structural hypotheses together.
/-- **Common primitive irreducible block decompositions after blocked-word reindexing.**

Assume the one-sided equality which identifies, for every common cyclic-sector
family, the canonically blocked weighted nonzero part with the same family written
using the reindexing of blocked physical words.  Then two tensors with the same
MPV family have one common positive blocking length whose nonzero parts are
weighted families of trace-preserving, primitive, tensor-irreducible blocks with
positive bond dimensions and nonzero weights.  At every positive length each
blocked tensor equals its nonzero part, and the two nonzero parts equal each
other.  The all-zero leftover block contributes only at length zero, so it is
omitted; the length-zero coefficient is restored once, at the end, from equality
of the bond dimensions.

The displayed reindexing equality is the remaining one-sided blocked-word
theorem; this result isolates the mathematical hypotheses used before the later
injectivity and BNT comparison. -/
theorem afterBlocking_commonPrimitiveIrreducibleBlocks_of_reindexedNonzeroParts
    {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B)
    (hReindexed : CommonSectorRelabelingHypothesis d) :
    ∃ p : ℕ, 0 < p ∧
    ∃ (rA : ℕ) (dimA : Fin rA → ℕ) (μA : Fin rA → ℂ)
      (blocksA : (x : Fin rA) → MPSTensor (blockPhysDim d p) (dimA x)),
    ∃ (rB : ℕ) (dimB : Fin rB → ℕ) (μB : Fin rB → ℂ)
      (blocksB : (x : Fin rB) → MPSTensor (blockPhysDim d p) (dimB x)),
      SameMPV₂Pos (blockTensor (d := d) (D := D₁) A p)
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) ∧
      SameMPV₂Pos (blockTensor (d := d) (D := D₂) B p)
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) ∧
      SameMPV₂Pos
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA)
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) ∧
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
  obtain ⟨p, hp, rA₀, dimA₀, μA₀, blocksA₀,
      rB₀, dimB₀, μB₀, blocksB₀, familyA, familyB,
      hFamilyA, hFamilyB, hAPosCanon, hBPosCanon, hPosCanon,
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
  have hAPos : SameMPV₂Pos (blockTensor (d := d) (D := D₁) A p) nonzeroA := by
    intro N hN σ
    exact (hAPosCanon N hN σ).trans (hFlatA N σ)
  have hBPos : SameMPV₂Pos (blockTensor (d := d) (D := D₂) B p) nonzeroB := by
    intro N hN σ
    exact (hBPosCanon N hN σ).trans (hFlatB N σ)
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
  refine ⟨p, hp,
    (∑ k : Fin rA₀, familyA.period k), familyA.commonFlatDim, familyA.commonFlatWeight μA₀,
    flatBlocksA,
    (∑ k : Fin rB₀, familyB.period k), familyB.commonFlatDim, familyB.commonFlatWeight μB₀,
    flatBlocksB,
    hAPos, hBPos, hNonzeroPos,
    hμA, hμB, hTPA', hTPB', hPrimA', hPrimB', hIrrA', hIrrB', hDimA, hDimB⟩

/-- **Unconditional common primitive irreducible block decompositions.**

The proof obtains the required relabeling assertion directly from the family-level
comparison between direct blocking and the common alphabet, then assembles the
blockwise equalities over the weighted direct sum.
-/
theorem unconditional_commonPrimitiveIrreducibleBlocks
    {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B) :
    ∃ p : ℕ, 0 < p ∧
    ∃ (rA : ℕ) (dimA : Fin rA → ℕ) (μA : Fin rA → ℂ)
      (blocksA : (x : Fin rA) → MPSTensor (blockPhysDim d p) (dimA x)),
    ∃ (rB : ℕ) (dimB : Fin rB → ℕ) (μB : Fin rB → ℂ)
      (blocksB : (x : Fin rB) → MPSTensor (blockPhysDim d p) (dimB x)),
      SameMPV₂Pos (blockTensor (d := d) (D := D₁) A p)
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) ∧
      SameMPV₂Pos (blockTensor (d := d) (D := D₂) B p)
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) ∧
      SameMPV₂Pos
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA)
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) ∧
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
  have h_relabel : CommonSectorRelabelingHypothesis d :=
    fun μ blocks F =>
      F.sameMPV₂_weightedCanonicalBlock_commonReindexedBlock_of_blockwise μ
        (fun k => F.blockTensor_sameMPV₂_commonReindexedBlock k)
  exact afterBlocking_commonPrimitiveIrreducibleBlocks_of_reindexedNonzeroParts
    A B hSame h_relabel

end MPSTensor

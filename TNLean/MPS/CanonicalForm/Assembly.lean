/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.Assembly.ProportionalComparison

/-!
# Canonical-form reduction after blocking

This module is the public entry point for the end-to-end canonical-form
reduction after blocking. It keeps the historical import path
`TNLean.MPS.CanonicalForm.Assembly` available while the underlying development is
split across focused supporting modules.

The supporting modules are:

* `TNLean.MPS.CanonicalForm.Assembly.TPPrimitiveReduction` — blocked
  TP-primitive decomposition from arbitrary input.
* `TNLean.MPS.CanonicalForm.Assembly.NormalityChain` — the normality chain for
  TP-primitive irreducible blocks and preservation of normality under blocking.
* `TNLean.MPS.CanonicalForm.Assembly.PrimitiveBlocks` — blocked irreducibility
  and the conditional weak block-matching theorem.
* `TNLean.MPS.CanonicalForm.Assembly.CommonBlockedCyclicSectorFamily` —
  common-period cyclic-sector family API.
* `TNLean.MPS.CanonicalForm.Assembly.CyclicSectorDecomposition` — cyclic sector
  decomposition after blocking.
* `TNLean.MPS.CanonicalForm.Assembly.StructuralData` — common-period blocking
  and structural after-blocking data.
* `TNLean.MPS.CanonicalForm.Assembly.StructuralTheorem` — historical re-export
  path for structural data and common-sector transport.
* `TNLean.MPS.CanonicalForm.Assembly.CommonSectorTransport` — zero-tail and
  common-sector transport after the structural theorem.
* `TNLean.MPS.CanonicalForm.Assembly.ProportionalComparison` — sector comparison
  from BNT proportional-decomposition data.

## Main statements

The imported modules provide the canonical-form reduction theorems, including
`exists_tp_primitive_blockDecomp_after_blocking`,
`isNormal_of_tp_primitive_irreducible`,
`isIrreducibleTensor_blockTensor_of_tp_primitive_irr`,
`exists_cyclic_sector_decomp_of_TP_of_isIrreducibleTensor`,
`primitive_and_irreducible_sectorBlocks_of_cyclic_decomp_after_blocking_of_projStep`,
`primitive_and_irreducible_sectorBlocks_of_cyclic_decomp_after_blocking_of_fixedAlgebraRigidity`,
`primitive_and_irreducible_sectorBlocks_of_cyclic_decomp_after_blocking`,
`bilateral_commonPeriod_blocking_tp_primitive_normal`, and
`afterBlocking_structuralData_of_sameMPV₂`.

This public entry point also records a conditional formulation of the
Cirac--Pérez-García--Schuch--Verstraete after-blocking theorem that does not
invoke the periodic Fundamental Theorem.  The structure
`AfterBlockingFundamentalTheoremHypotheses` names the remaining comparison inputs,
while `fundamentalTheorem_afterBlocking_of_comparisonHypotheses` gives the
corresponding sector-decomposition conclusion: after blocking, the two tensors
are represented by BNT sector decompositions whose basis sectors and weights
match up to permutation and nonzero phases.

## References

* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608, Section 2.3 + Appendix A]
* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:2011.12127, Section IV]

## Tags

matrix product states, canonical form, blocking, primitive transfer maps
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace MPSTensor

/-- Remaining hypotheses for the after-blocking Fundamental Theorem formulation.

Starting from `SameMPV₂ A B`, the present derivation constructs common primitive
nonzero-sector families after a common blocking.  The blocked-word relabeling assertion is now
derived in this formulation from the grouped-block cast theorem.  To reach the sector-weight
conclusion of the Cirac--Pérez-García--Schuch--Verstraete Fundamental Theorem for exactly those
produced families, one still needs comparison data for those produced families.  The field
`comparison` is supplied with their trace-preserving, primitive, irreducible, and positive
bond-dimension evidence, so the remaining assumptions cannot be applied to a different
decomposition. -/
structure AfterBlockingFundamentalTheoremHypotheses
    {d D₁ D₂ : ℕ} (A : MPSTensor d D₁) (B : MPSTensor d D₂) : Prop where
  /-- The remaining BNT-cover comparison data for the produced common primitive
  nonzero-sector families, with the structural evidence for trace preservation,
  primitivity, irreducibility, and positive bond dimensions supplied. -/
  comparison : ∀ {p zeroTailA zeroTailB rA rB : ℕ}
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
            (DtotA := DtotA) (DtotB := DtotB) μA μB blocksA blocksB)

/-- Conclusion of the conditional after-blocking Fundamental Theorem formulation.

The conclusion follows the Cirac--Pérez-García--Schuch--Verstraete statement at the level of
BNT sector decompositions.  After one positive blocking, there are sector decompositions `P` and
`Q` with BNT data.  The blocked tensors agree with these sector tensors at all positive lengths,
the two sector tensors generate the same full MPV family, and the basis sectors have matching
multiplicities and weights up to a permutation and nonzero phases.

The positive-length comparison with the original blocked tensors is intentional: before the
zero-tail dimensions are identified, the zero-tail contribution is the only obstruction at
length zero. -/
structure AfterBlockingFundamentalTheoremConclusion
    {d D₁ D₂ : ℕ} (A : MPSTensor d D₁) (B : MPSTensor d D₂) where
  /-- The common physical blocking length. -/
  p : ℕ
  /-- The blocking length is positive. -/
  p_pos : 0 < p
  /-- The sector decomposition representing the left blocked tensor. -/
  P : SectorDecomposition (blockPhysDim d p)
  /-- The sector decomposition representing the right blocked tensor. -/
  Q : SectorDecomposition (blockPhysDim d p)
  /-- The left blocked tensor agrees with its sector tensor at positive lengths. -/
  left_mpv : SameMPV₂Pos (blockTensor (d := d) (D := D₁) A p) P.toTensor
  /-- The right blocked tensor agrees with its sector tensor at positive lengths. -/
  right_mpv : SameMPV₂Pos (blockTensor (d := d) (D := D₂) B p) Q.toTensor
  /-- The two sector tensors generate the same full MPV family. -/
  sector_mpv : SameMPV₂ P.toTensor Q.toTensor
  /-- The left sector decomposition carries BNT data. -/
  left_bnt : HasBNTSectorData P
  /-- The right sector decomposition carries BNT data. -/
  right_bnt : HasBNTSectorData Q
  /-- The matching of BNT sectors. -/
  perm : Fin P.basisCount ≃ Fin Q.basisCount
  /-- Matched BNT sectors have the same multiplicity. -/
  copies_eq : ∀ j, P.copies j = Q.copies (perm j)
  /-- The nonzero phase relating each matched sector. -/
  phase : Fin P.basisCount → ℂ
  /-- The sector phases are nonzero. -/
  phase_ne_zero : ∀ j, phase j ≠ 0
  /-- Sector weights match as multisets after multiplying the right weights by the sector phase. -/
  weight_multiset_eq : ∀ j : Fin P.basisCount,
    Finset.univ.val.map (P.weight j) =
      Finset.univ.val.map
        (fun q => phase j * Q.weight (perm j) (Fin.cast (copies_eq j) q))

/-- **Conditional after-blocking Fundamental Theorem formulation.**

Let `A` and `B` generate the same MPV family.  Under the explicit remaining comparison
hypotheses, there is a positive blocking after which the two tensors admit BNT sector
decompositions with the same sector MPV family, matched basis-sector multiplicities, and matched
sector-weight multisets up to nonzero phases.  This is the conditional formulation proved by the
present periodic-theorem-free derivation: it is a direct consequence of
`afterBlocking_sectorComparison_zeroTail_of_reindexedNonzeroParts_bntCover`, not a hidden
assumption or an appeal to the periodic Fundamental Theorem. -/
theorem fundamentalTheorem_afterBlocking_of_comparisonHypotheses
    {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B)
    (h : AfterBlockingFundamentalTheoremHypotheses A B) :
    Nonempty (AfterBlockingFundamentalTheoremConclusion A B) := by
  have h_group : CommonGroupedBlockCastHypothesis d :=
    CommonGroupedBlockCastHypothesis.of_flattenWordOfBlock_cast_eq d
  have h_relabel : CommonSectorRelabelingHypothesis d :=
    h_group.toRelabelingHypothesis
  obtain ⟨p, hp, P, Q, hA, hB, hPQ, hPbnt, hQbnt,
      perm, hCopies, phase, hPhase, hWeights⟩ :=
    afterBlocking_sectorComparison_zeroTail_of_reindexedNonzeroParts_bntCover
      A B hSame h_relabel h.comparison
  exact ⟨{
    p := p
    p_pos := hp
    P := P
    Q := Q
    left_mpv := hA
    right_mpv := hB
    sector_mpv := hPQ
    left_bnt := hPbnt
    right_bnt := hQbnt
    perm := perm
    copies_eq := hCopies
    phase := phase
    phase_ne_zero := hPhase
    weight_multiset_eq := hWeights }⟩

end MPSTensor

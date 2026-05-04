/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.Assembly.StructuralTheorem

open scoped Matrix BigOperators ComplexOrder MatrixOrder

/-!
# Sector comparisons from common MPV phase covers

The results here give after-blocking sector-comparison consequences from finite-length span
comparisons and common MPV phase covers, and record the special case where the cover comes from a
BNT proportional-decomposition comparison of the nonzero-weight block families.

## Main statements

* `afterBlocking_sectorComparison_of_proportionalDecompositionConclusion` — exact
  nonzero part decompositions plus BNT proportional-decomposition data imply the sector-weight
  comparison.
* `afterBlocking_sectorComparison_zeroTail_of_blockSpan` — zero-tail identities plus
  finite-length MPV span equality for the nonzero part imply the sector-weight comparison.
* `afterBlocking_sectorComparison_zeroTail_of_commonPhaseCover` — zero-tail decompositions
  plus common MPV phase-cover data imply the same sector-weight comparison.
* `afterBlocking_sectorComparison_zeroTail_of_reindexedNonzeroParts_commonPhaseCover` — the
  common-length cyclic-sector output, together with the blocked-word relabeling
  equality and the remaining zero-tail, injectivity, and common-cover assertions,
  implies the sector-weight comparison.
* `sectorBasisOverlapSpanHypotheses_of_reindexedNonzeroParts_bntCover` — the same
  common-length cyclic-sector output, with the overlap-span hypotheses obtained from
  BNT-cover data.
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

/-- Remaining two-sided hypotheses for common primitive nonzero-sector families.

The common-sector structural theorem supplies zero-tail decompositions, positive-length
nonzero-part equality, nonzero weights, trace-preserving normalization, primitive transfer maps,
irreducibility, and positive bond dimensions. To pass to the overlap-rigidity sector comparison
one still needs equality of zero-tail dimensions, one-site injectivity for the two block families,
and equality of their finite-length MPV spans. -/
structure CommonPrimitiveSpanHypotheses
    {d p rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    (zeroTailA zeroTailB : ℕ)
    (blocksA : (x : Fin rA) → MPSTensor (blockPhysDim d p) (dimA x))
    (blocksB : (x : Fin rB) → MPSTensor (blockPhysDim d p) (dimB x)) : Prop where
  /-- The two zero-tail dimensions agree. -/
  zeroTail_eq : zeroTailA = zeroTailB
  /-- The left nonzero-sector blocks are one-site injective. -/
  left_injective : ∀ x : Fin rA, IsInjective (blocksA x)
  /-- The right nonzero-sector blocks are one-site injective. -/
  right_injective : ∀ x : Fin rB, IsInjective (blocksB x)
  /-- The two nonzero-sector block families have the same finite-length MPV spans. -/
  span_eq : ∀ N,
    Submodule.span ℂ (Set.range (fun x : Fin rA =>
      mpvState (d := blockPhysDim d p) (blocksA x) N)) =
    Submodule.span ℂ (Set.range (fun x : Fin rB =>
      mpvState (d := blockPhysDim d p) (blocksB x) N))

namespace CommonPrimitiveSpanHypotheses

/-- A common MPV phase cover supplies the span field in the common primitive hypotheses. -/
theorem of_commonPhaseCover
    {d p rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {zeroTailA zeroTailB : ℕ}
    {blocksA : (x : Fin rA) → MPSTensor (blockPhysDim d p) (dimA x)}
    {blocksB : (x : Fin rB) → MPSTensor (blockPhysDim d p) (dimB x)}
    (hZeroTail : zeroTailA = zeroTailB)
    (hInjA : ∀ x : Fin rA, IsInjective (blocksA x))
    (hInjB : ∀ x : Fin rB, IsInjective (blocksB x))
    (cover : MPVCommonPhaseCover blocksA blocksB) :
    CommonPrimitiveSpanHypotheses zeroTailA zeroTailB blocksA blocksB where
  zeroTail_eq := hZeroTail
  left_injective := hInjA
  right_injective := hInjB
  span_eq := fun N => cover.span_eq N

end CommonPrimitiveSpanHypotheses

/-- Remaining two-sided hypotheses for common primitive nonzero-sector families,
formulated with a common MPV phase cover.

This is the common-cover variant of `CommonPrimitiveSpanHypotheses`: the structural
theorem supplies the same primitive nonzero-sector data, while the remaining inputs
are equality of the zero-tail dimensions, one-site injectivity on both sides, and a
common phase cover for the two block families. -/
structure CommonPrimitivePhaseCoverHypotheses
    {d p rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    (zeroTailA zeroTailB : ℕ)
    (blocksA : (x : Fin rA) → MPSTensor (blockPhysDim d p) (dimA x))
    (blocksB : (x : Fin rB) → MPSTensor (blockPhysDim d p) (dimB x)) : Prop where
  /-- The two zero-tail dimensions agree. -/
  zeroTail_eq : zeroTailA = zeroTailB
  /-- The left nonzero-sector blocks are one-site injective. -/
  left_injective : ∀ x : Fin rA, IsInjective (blocksA x)
  /-- The right nonzero-sector blocks are one-site injective. -/
  right_injective : ∀ x : Fin rB, IsInjective (blocksB x)
  /-- The two nonzero-sector block families admit a common MPV phase cover. -/
  cover : Nonempty (MPVCommonPhaseCover blocksA blocksB)

namespace CommonPrimitivePhaseCoverHypotheses

/-- A common MPV phase cover hypothesis implies the corresponding span hypothesis. -/
theorem toSpanHypotheses
    {d p rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {zeroTailA zeroTailB : ℕ}
    {blocksA : (x : Fin rA) → MPSTensor (blockPhysDim d p) (dimA x)}
    {blocksB : (x : Fin rB) → MPSTensor (blockPhysDim d p) (dimB x)}
    (h : CommonPrimitivePhaseCoverHypotheses zeroTailA zeroTailB blocksA blocksB) :
    CommonPrimitiveSpanHypotheses zeroTailA zeroTailB blocksA blocksB := by
  obtain ⟨cover⟩ := h.cover
  exact CommonPrimitiveSpanHypotheses.of_commonPhaseCover
    h.zeroTail_eq h.left_injective h.right_injective cover

end CommonPrimitivePhaseCoverHypotheses

/-- Remaining two-sided hypotheses for common primitive nonzero-sector families,
formulated with a BNT proportional-decomposition comparison.

This is the proportional-comparison version of `CommonPrimitivePhaseCoverHypotheses`: the
structural theorem supplies the same primitive nonzero-sector data, while the remaining inputs
are equality of the zero-tail dimensions, one-site injectivity on both sides, and a
BNT comparison conclusion for the two block families. -/
structure CommonPrimitiveProportionalHypotheses
    {d p rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    (zeroTailA zeroTailB : ℕ)
    (blocksA : (x : Fin rA) → MPSTensor (blockPhysDim d p) (dimA x))
    (blocksB : (x : Fin rB) → MPSTensor (blockPhysDim d p) (dimB x)) : Prop where
  /-- The two zero-tail dimensions agree. -/
  zeroTail_eq : zeroTailA = zeroTailB
  /-- The left nonzero-sector blocks are one-site injective. -/
  left_injective : ∀ x : Fin rA, IsInjective (blocksA x)
  /-- The right nonzero-sector blocks are one-site injective. -/
  right_injective : ∀ x : Fin rB, IsInjective (blocksB x)
  /-- The two nonzero-sector block families satisfy the BNT proportional comparison conclusion. -/
  proportional : ProportionalDecompositionConclusion (d := blockPhysDim d p) blocksA blocksB

namespace CommonPrimitiveProportionalHypotheses

/-- A proportional-decomposition comparison gives the corresponding phase-cover hypotheses. -/
theorem toPhaseCoverHypotheses
    {d p rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {zeroTailA zeroTailB : ℕ}
    {blocksA : (x : Fin rA) → MPSTensor (blockPhysDim d p) (dimA x)}
    {blocksB : (x : Fin rB) → MPSTensor (blockPhysDim d p) (dimB x)}
    (h : CommonPrimitiveProportionalHypotheses zeroTailA zeroTailB blocksA blocksB) :
    CommonPrimitivePhaseCoverHypotheses zeroTailA zeroTailB blocksA blocksB where
  zeroTail_eq := h.zeroTail_eq
  left_injective := h.left_injective
  right_injective := h.right_injective
  cover := nonempty_mpvCommonPhaseCover_of_proportionalDecompositionConclusion
    (d := blockPhysDim d p) blocksA blocksB h.proportional

/-- A proportional-decomposition comparison gives the corresponding span hypotheses. -/
theorem toSpanHypotheses
    {d p rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {zeroTailA zeroTailB : ℕ}
    {blocksA : (x : Fin rA) → MPSTensor (blockPhysDim d p) (dimA x)}
    {blocksB : (x : Fin rB) → MPSTensor (blockPhysDim d p) (dimB x)}
    (h : CommonPrimitiveProportionalHypotheses zeroTailA zeroTailB blocksA blocksB) :
    CommonPrimitiveSpanHypotheses zeroTailA zeroTailB blocksA blocksB :=
  h.toPhaseCoverHypotheses.toSpanHypotheses

end CommonPrimitiveProportionalHypotheses

/-- Remaining BNT-level inputs for constructing a common MPV phase cover
from the common-length cyclic sector families produced by the structural theorem.

The structural theorem
`afterBlocking_commonPrimitiveIrreducibleBlocks_of_reindexedNonzeroParts`
supplies trace-preserving, primitive, tensor-irreducible block families
with nonzero weights and positive bond dimensions at a common blocking
length.  The four fields below are the additional BNT hypotheses needed
to compare the two families and obtain a common MPV phase cover.

The remaining mathematical tasks are:
1. Verify `IsNormalCanonicalForm` for the produced block families
   (requires ordering the weights by decreasing modulus).
2. Verify `BlocksNotGaugePhaseEquiv` for the cyclic-sector block families
   (follows from the fact that distinct cyclic sectors carry
   distinct peripheral eigenvalues and therefore cannot be
   gauge-phase equivalent).
3. Construct `ProportionalDecompositionData` from the `SameMPV₂`
   equality of the two nonzero parts, which is available from the
   structural theorem and the zero-tail identity. -/
structure CommonPrimitiveBNTCoverHypotheses
    {d p rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {zeroTailA zeroTailB DtotA DtotB : ℕ}
    (μA : Fin rA → ℂ) (μB : Fin rB → ℂ)
    (blocksA : (x : Fin rA) → MPSTensor (blockPhysDim d p) (dimA x))
    (blocksB : (x : Fin rB) → MPSTensor (blockPhysDim d p) (dimB x)) : Type where
  /-- The left block family is in normal canonical form. -/
  ncfA : IsNormalCanonicalForm (d := blockPhysDim d p) μA blocksA
  /-- The right block family is in normal canonical form. -/
  ncfB : IsNormalCanonicalForm (d := blockPhysDim d p) μB blocksB
  /-- Distinct left blocks are not gauge-phase equivalent. -/
  notGpeA : BlocksNotGaugePhaseEquiv (d := blockPhysDim d p) blocksA
  /-- Distinct right blocks are not gauge-phase equivalent. -/
  notGpeB : BlocksNotGaugePhaseEquiv (d := blockPhysDim d p) blocksB
  /-- The two zero-tail dimensions agree. -/
  zeroTail_eq : zeroTailA = zeroTailB
  /-- The two nonzero-sector block families are one-site injective. -/
  left_injective : ∀ x : Fin rA, IsInjective (blocksA x)
  /-- The two nonzero-sector block families are one-site injective. -/
  right_injective : ∀ x : Fin rB, IsInjective (blocksB x)
  /-- Proportional decomposition data linking the two block families. -/
  decompData : ProportionalDecompositionData (d := blockPhysDim d p)
    blocksA blocksB DtotA DtotB

namespace CommonPrimitiveBNTCoverHypotheses

/-- Form `CommonPrimitiveBNTCoverHypotheses` from common primitive structural data
and explicit BNT comparison inputs. -/
def ofCommonPrimitiveData
    {d p rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {zeroTailA zeroTailB DtotA DtotB : ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    {blocksA : (x : Fin rA) → MPSTensor (blockPhysDim d p) (dimA x)}
    {blocksB : (x : Fin rB) → MPSTensor (blockPhysDim d p) (dimB x)}
    (hμA : ∀ x, μA x ≠ 0)
    (hμB : ∀ x, μB x ≠ 0)
    (hTPA : ∀ x, ∑ i : Fin (blockPhysDim d p), (blocksA x i)ᴴ * blocksA x i = 1)
    (hTPB : ∀ x, ∑ i : Fin (blockPhysDim d p), (blocksB x i)ᴴ * blocksB x i = 1)
    (hPrimA : ∀ x, _root_.IsPrimitive
      (transferMap (d := blockPhysDim d p) (D := dimA x) (blocksA x)))
    (hPrimB : ∀ x, _root_.IsPrimitive
      (transferMap (d := blockPhysDim d p) (D := dimB x) (blocksB x)))
    (hIrrA : ∀ x, IsIrreducibleTensor (blocksA x))
    (hIrrB : ∀ x, IsIrreducibleTensor (blocksB x))
    (hAntiA : StrictAnti (fun x : Fin rA => ‖μA x‖))
    (hAntiB : StrictAnti (fun x : Fin rB => ‖μB x‖))
    (hNotGpeA : BlocksNotGaugePhaseEquiv (d := blockPhysDim d p) blocksA)
    (hNotGpeB : BlocksNotGaugePhaseEquiv (d := blockPhysDim d p) blocksB)
    (hZeroTail : zeroTailA = zeroTailB)
    (hInjA : ∀ x, IsInjective (blocksA x))
    (hInjB : ∀ x, IsInjective (blocksB x))
    (hDecomp : ProportionalDecompositionData (d := blockPhysDim d p)
      blocksA blocksB DtotA DtotB) :
    CommonPrimitiveBNTCoverHypotheses (zeroTailA := zeroTailA) (zeroTailB := zeroTailB)
      (DtotA := DtotA) (DtotB := DtotB) μA μB blocksA blocksB where
  ncfA := by
    have hDimA : ∀ x, 0 < dimA x := fun x => Nat.pos_of_ne_zero (NeZero.ne (dimA x))
    exact isNormalCanonicalForm_of_tp_primitive_irr_sorted
      (d' := blockPhysDim d p) (μ := μA) blocksA hTPA hPrimA hDimA hμA hIrrA hAntiA
  ncfB := by
    have hDimB : ∀ x, 0 < dimB x := fun x => Nat.pos_of_ne_zero (NeZero.ne (dimB x))
    exact isNormalCanonicalForm_of_tp_primitive_irr_sorted
      (d' := blockPhysDim d p) (μ := μB) blocksB hTPB hPrimB hDimB hμB hIrrB hAntiB
  notGpeA := hNotGpeA
  notGpeB := hNotGpeB
  zeroTail_eq := hZeroTail
  left_injective := hInjA
  right_injective := hInjB
  decompData := hDecomp

/-- A BNT cover hypothesis bundle produces a common MPV phase cover. -/
theorem toMPVCommonPhaseCover
    {d p rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {zeroTailA zeroTailB DtotA DtotB : ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    {blocksA : (x : Fin rA) → MPSTensor (blockPhysDim d p) (dimA x)}
    {blocksB : (x : Fin rB) → MPSTensor (blockPhysDim d p) (dimB x)}
    (h : CommonPrimitiveBNTCoverHypotheses (zeroTailA := zeroTailA) (zeroTailB := zeroTailB)
      (DtotA := DtotA) (DtotB := DtotB) μA μB blocksA blocksB) :
    Nonempty (MPVCommonPhaseCover blocksA blocksB) :=
  nonempty_mpvCommonPhaseCover_of_separated_normalCFBNT_data
    (d := blockPhysDim d p) blocksA blocksB
    h.ncfA h.notGpeA h.ncfB h.notGpeB h.decompData

/-- A BNT cover hypothesis bundle produces the common primitive phase-cover hypotheses. -/
theorem toCommonPrimitivePhaseCoverHypotheses
    {d p rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {zeroTailA zeroTailB DtotA DtotB : ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    {blocksA : (x : Fin rA) → MPSTensor (blockPhysDim d p) (dimA x)}
    {blocksB : (x : Fin rB) → MPSTensor (blockPhysDim d p) (dimB x)}
    (h : CommonPrimitiveBNTCoverHypotheses (zeroTailA := zeroTailA) (zeroTailB := zeroTailB)
      (DtotA := DtotA) (DtotB := DtotB) μA μB blocksA blocksB) :
    CommonPrimitivePhaseCoverHypotheses zeroTailA zeroTailB blocksA blocksB where
  zeroTail_eq := h.zeroTail_eq
  left_injective := h.left_injective
  right_injective := h.right_injective
  cover := h.toMPVCommonPhaseCover

end CommonPrimitiveBNTCoverHypotheses

/-- **Sector comparison from BNT proportional-decomposition data.**

A proportional-decomposition comparison supplies a common MPV phase cover of the two
nonzero-weight block families. Therefore the common-cover sector theorem applies without an
extra finite-length span hypothesis. -/
theorem afterBlocking_sectorComparison_of_proportionalDecompositionConclusion
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
    (hMatch : ProportionalDecompositionConclusion (d := blockPhysDim d p) blocksA blocksB)
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
  obtain ⟨cover⟩ := nonempty_mpvCommonPhaseCover_of_proportionalDecompositionConclusion
    (d := blockPhysDim d p) blocksA blocksB hMatch
  exact fundamentalTheorem_after_blocking_sector_of_common_blocks_commonPhaseCover
    A B hSame hp μA blocksA μB blocksB cover hAblocks hBblocks hTPA hTPB hIrrA hIrrB
    hPrimA hPrimB hInjA hInjB hμA hμB

/-- **Zero-tail sector comparison from finite-length nonzero-block span equality.**

This zero-tail-aware variant combines exact zero-tail identities with equality of the
finite-length MPV spans of the two nonzero-weight block families. The span equality supplies the
last two-family hypothesis needed by the phase-class BNT representative construction; the
zero-tail equality gives full equality of the two nonzero parts, including length zero. -/
theorem afterBlocking_sectorComparison_zeroTail_of_blockSpan
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
  let nonzeroA := toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA
  let nonzeroB := toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB
  obtain ⟨P, Q, hPblocks, hQblocks, hPbnt, hQbnt, hOverlapSpan⟩ :=
    exists_bnt_sectorDecomp_pair_with_overlapSpan_of_block_span_eq
      (d := blockPhysDim d p) μA blocksA μB blocksB hTPA hTPB hIrrA hIrrB
      hPrimA hPrimB hInjA hInjB hμA hμB hBlockSpan
  have hAB : SameMPV₂ (blockTensor (d := d) (D := D₁) A p)
                      (blockTensor (d := d) (D := D₂) B p) :=
    sameMPV₂_blockTensor A B hSame p
  have hNonzero : SameMPV₂ nonzeroA nonzeroB :=
    sameMPV₂_live_of_sameMPV₂_with_zeroTail_eq
      (blockTensor (d := d) (D := D₁) A p)
      (blockTensor (d := d) (D := D₂) B p)
      nonzeroA nonzeroB hAB hAblocks hBblocks hZeroTail
  have hPeqPos : SameMPV₂Pos (blockTensor (d := d) (D := D₁) A p) P.toTensor := by
    intro N hN σ
    have hZero :
        mpv (zeroMPSTensor (blockPhysDim d p) zeroTailA) σ = 0 := by
      rw [mpv_zeroMPSTensor]
      simp [Nat.ne_of_gt hN]
    calc
      mpv (blockTensor (d := d) (D := D₁) A p) σ
          = mpv (zeroMPSTensor (blockPhysDim d p) zeroTailA) σ + mpv nonzeroA σ :=
            hAblocks N σ
      _ = mpv nonzeroA σ := by rw [hZero]; simp
      _ = mpv P.toTensor σ := (hPblocks N σ).symm
  have hQeqPos : SameMPV₂Pos (blockTensor (d := d) (D := D₂) B p) Q.toTensor := by
    intro N hN σ
    have hZero :
        mpv (zeroMPSTensor (blockPhysDim d p) zeroTailB) σ = 0 := by
      rw [mpv_zeroMPSTensor]
      simp [Nat.ne_of_gt hN]
    calc
      mpv (blockTensor (d := d) (D := D₂) B p) σ
          = mpv (zeroMPSTensor (blockPhysDim d p) zeroTailB) σ + mpv nonzeroB σ :=
            hBblocks N σ
      _ = mpv nonzeroB σ := by rw [hZero]; simp
      _ = mpv Q.toTensor σ := (hQblocks N σ).symm
  have hPQeq : SameMPV₂ P.toTensor Q.toTensor := by
    intro N σ
    calc
      mpv P.toTensor σ = mpv nonzeroA σ := hPblocks N σ
      _ = mpv nonzeroB σ := hNonzero N σ
      _ = mpv Q.toTensor σ := (hQblocks N σ).symm
  obtain ⟨M⟩ := hOverlapSpan.exists_sectorBasisMatching hPQeq
  obtain ⟨ζ, hζne, hMultiset⟩ :=
    fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_sectorMatching M hPbnt hPQeq
  exact ⟨p, hp, P, Q, hPeqPos, hQeqPos, hPQeq, hPbnt, hQbnt,
          M.perm, M.copies_eq, ζ, hζne, hMultiset⟩

/-- **Zero-tail sector comparison from common MPV phase-cover data.**

This zero-tail-aware variant combines exact zero-tail decompositions with a common MPV phase
cover of the nonzero-weight block families. The cover gives the finite-length span equality for
those families, and the block-span theorem then gives the sector-weight comparison. -/
theorem afterBlocking_sectorComparison_zeroTail_of_commonPhaseCover
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
    (cover : MPVCommonPhaseCover blocksA blocksB)
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
    (hInjA : ∀ k, IsInjective (blocksA k))
    (hInjB : ∀ k, IsInjective (blocksB k))
    (hμA : ∀ k, μA k ≠ 0)
    (hμB : ∀ k, μB k ≠ 0) :
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
              (fun q => ζ j * Q.weight (perm j) (Fin.cast (hCopies j) q)) :=
  afterBlocking_sectorComparison_zeroTail_of_blockSpan
    A B hSame hp μA blocksA μB blocksB hAblocks hBblocks hZeroTail hTPA hTPB
    hIrrA hIrrB hPrimA hPrimB hInjA hInjB hμA hμB (fun N => cover.span_eq N)

/-- **Zero-tail sector comparison from BNT proportional-decomposition data.**

This zero-tail-aware variant combines the exact nonzero part cancellation step with the BNT
proportional-decomposition comparison. The proportional comparison gives the common MPV phase
cover, hence the finite-length span equality for the nonzero part; injectivity supplies the
remaining overlap-span hypothesis. -/
theorem afterBlocking_sectorComparison_zeroTail_of_proportionalDecompositionConclusion
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
    (hInjA : ∀ k, IsInjective (blocksA k))
    (hInjB : ∀ k, IsInjective (blocksB k))
    (hμA : ∀ k, μA k ≠ 0)
    (hμB : ∀ k, μB k ≠ 0)
    (hMatch : ProportionalDecompositionConclusion (d := blockPhysDim d p) blocksA blocksB) :
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
  obtain ⟨cover⟩ := nonempty_mpvCommonPhaseCover_of_proportionalDecompositionConclusion
    (d := blockPhysDim d p) blocksA blocksB hMatch
  exact afterBlocking_sectorComparison_zeroTail_of_commonPhaseCover
    A B hSame hp μA blocksA μB blocksB cover hAblocks hBblocks hZeroTail
    hTPA hTPB hIrrA hIrrB hPrimA hPrimB hInjA hInjB hμA hμB

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

/-- **Sector basis overlap-span data from common primitive nonzero-sector families.**

The common primitive irreducible block theorem supplies the two nonzero-sector decompositions
obtained after blocked-word reindexing. If the remaining zero-tail equality, one-site
injectivity, and finite-length span equality are supplied for those same families, the
collapsed BNT representative construction produces a pair of sector decompositions satisfying
`SectorBasisOverlapSpanHypotheses`.

This theorem isolates the `SectorBasisOverlapSpanHypotheses` construction used internally by
`afterBlocking_sectorComparison_zeroTail_of_reindexedNonzeroParts_spanHypotheses`. The
conclusion records the nonzero-block MPV agreements, the BNT linear-independence data, and
the eleven overlap-span fields: nonzero bond dimensions, injectivity, left-canonical
normalization, asymptotic self- and off-diagonal overlaps, and equality of the finite-length
MPV spans of the two sector bases.

The `hRemaining` function must supply `CommonPrimitiveSpanHypotheses` for the block families
produced by `afterBlocking_commonPrimitiveIrreducibleBlocks_of_reindexedNonzeroParts`.
Concretely it needs to prove equality of the two zero-tail dimensions, one-site injectivity
of the nonzero-weight blocks, and equality of their finite-length MPV spans. The last of
these can be supplied by a common MPV phase cover (via
`CommonPrimitiveSpanHypotheses.of_commonPhaseCover`) or by a BNT proportional-decomposition
comparison (via `CommonPrimitiveProportionalHypotheses.toSpanHypotheses`). -/
theorem sectorBasisOverlapSpanHypotheses_of_reindexedNonzeroParts
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
    ∃ p : ℕ, 0 < p ∧
    ∃ P Q : SectorDecomposition (blockPhysDim d p),
      SameMPV₂ P.toTensor Q.toTensor ∧
      HasBNTSectorData P ∧ HasBNTSectorData Q ∧
      SectorBasisOverlapSpanHypotheses P Q := by
  obtain ⟨p, hp, zeroTailA, zeroTailB, rA, dimA, μA, blocksA,
      rB, dimB, μB, blocksB, hAblocks, hBblocks, hAPos, hBPos, hNonzeroPos,
      hZero, hμA, hμB, hTPA, hTPB, hPrimA, hPrimB, hIrrA, hIrrB, hDimA, hDimB⟩ :=
    afterBlocking_commonPrimitiveIrreducibleBlocks_of_reindexedNonzeroParts A B hSame hReindexed
  have hHyp : CommonPrimitiveSpanHypotheses zeroTailA zeroTailB blocksA blocksB :=
    hRemaining hp hAblocks hBblocks hAPos hBPos hNonzeroPos hZero hμA hμB hTPA hTPB
      hPrimA hPrimB hIrrA hIrrB hDimA hDimB
  letI : ∀ x : Fin rA, NeZero (dimA x) := fun x => ⟨Nat.ne_of_gt (hDimA x)⟩
  letI : ∀ x : Fin rB, NeZero (dimB x) := fun x => ⟨Nat.ne_of_gt (hDimB x)⟩
  let nonzeroA := toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA
  let nonzeroB := toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB
  have hAB : SameMPV₂ (blockTensor (d := d) (D := D₁) A p)
                      (blockTensor (d := d) (D := D₂) B p) :=
    sameMPV₂_blockTensor A B hSame p
  have hNonzero : SameMPV₂ nonzeroA nonzeroB :=
    sameMPV₂_live_of_sameMPV₂_with_zeroTail_eq
      (blockTensor (d := d) (D := D₁) A p)
      (blockTensor (d := d) (D := D₂) B p)
      nonzeroA nonzeroB hAB hAblocks hBblocks hHyp.zeroTail_eq
  obtain ⟨P, Q, hPblocks, hQblocks, hPbnt, hQbnt, hOverlapSpan⟩ :=
    exists_bnt_sectorDecomp_pair_with_overlapSpan_of_block_span_eq
      (d := blockPhysDim d p) μA blocksA μB blocksB hTPA hTPB hIrrA hIrrB
      hPrimA hPrimB hHyp.left_injective hHyp.right_injective hμA hμB hHyp.span_eq
  have hPQeq : SameMPV₂ P.toTensor Q.toTensor := by
    intro N σ
    calc
      mpv P.toTensor σ = mpv nonzeroA σ := hPblocks N σ
      _ = mpv nonzeroB σ := hNonzero N σ
      _ = mpv Q.toTensor σ := (hQblocks N σ).symm
  exact ⟨p, hp, P, Q, hPQeq, hPbnt, hQbnt, hOverlapSpan⟩

/-- **Sector basis overlap-span data via a common MPV phase cover.**

This is the common-phase-cover variant of
`sectorBasisOverlapSpanHypotheses_of_reindexedNonzeroParts`. Instead of requiring the
finite-length span equality directly, it asks for a common MPV phase cover of the two
nonzero-weight block families. The cover supplies the span equality through
`MPVCommonPhaseCover.span_eq`. -/
theorem sectorBasisOverlapSpanHypotheses_of_reindexedNonzeroParts_commonPhaseCover
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
    ∃ p : ℕ, 0 < p ∧
    ∃ P Q : SectorDecomposition (blockPhysDim d p),
      SameMPV₂ P.toTensor Q.toTensor ∧
      HasBNTSectorData P ∧ HasBNTSectorData Q ∧
      SectorBasisOverlapSpanHypotheses P Q := by
  obtain ⟨p, hp, zeroTailA, zeroTailB, rA, dimA, μA, blocksA,
      rB, dimB, μB, blocksB, hAblocks, hBblocks, hAPos, hBPos, hNonzeroPos,
      hZero, hμA, hμB, hTPA, hTPB, hPrimA, hPrimB, hIrrA, hIrrB, hDimA, hDimB⟩ :=
    afterBlocking_commonPrimitiveIrreducibleBlocks_of_reindexedNonzeroParts A B hSame hReindexed
  have hHyp : CommonPrimitivePhaseCoverHypotheses zeroTailA zeroTailB blocksA blocksB :=
    hRemaining hp hAblocks hBblocks hAPos hBPos hNonzeroPos hZero hμA hμB hTPA hTPB
      hPrimA hPrimB hIrrA hIrrB hDimA hDimB
  have hSpanHyp : CommonPrimitiveSpanHypotheses zeroTailA zeroTailB blocksA blocksB :=
    hHyp.toSpanHypotheses
  letI : ∀ x : Fin rA, NeZero (dimA x) := fun x => ⟨Nat.ne_of_gt (hDimA x)⟩
  letI : ∀ x : Fin rB, NeZero (dimB x) := fun x => ⟨Nat.ne_of_gt (hDimB x)⟩
  let nonzeroA := toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA
  let nonzeroB := toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB
  have hAB : SameMPV₂ (blockTensor (d := d) (D := D₁) A p)
                      (blockTensor (d := d) (D := D₂) B p) :=
    sameMPV₂_blockTensor A B hSame p
  have hNonzero : SameMPV₂ nonzeroA nonzeroB :=
    sameMPV₂_live_of_sameMPV₂_with_zeroTail_eq
      (blockTensor (d := d) (D := D₁) A p)
      (blockTensor (d := d) (D := D₂) B p)
      nonzeroA nonzeroB hAB hAblocks hBblocks hSpanHyp.zeroTail_eq
  obtain ⟨P, Q, hPblocks, hQblocks, hPbnt, hQbnt, hOverlapSpan⟩ :=
    exists_bnt_sectorDecomp_pair_with_overlapSpan_of_block_span_eq
      (d := blockPhysDim d p) μA blocksA μB blocksB hTPA hTPB hIrrA hIrrB
      hPrimA hPrimB hSpanHyp.left_injective hSpanHyp.right_injective hμA hμB hSpanHyp.span_eq
  have hPQeq : SameMPV₂ P.toTensor Q.toTensor := by
    intro N σ
    calc
      mpv P.toTensor σ = mpv nonzeroA σ := hPblocks N σ
      _ = mpv nonzeroB σ := hNonzero N σ
      _ = mpv Q.toTensor σ := (hQblocks N σ).symm
  exact ⟨p, hp, P, Q, hPQeq, hPbnt, hQbnt, hOverlapSpan⟩

/-- **Sector basis overlap-span data via BNT-cover hypotheses.**

This is the BNT-cover variant of
`sectorBasisOverlapSpanHypotheses_of_reindexedNonzeroParts_commonPhaseCover`.
The remaining input provides the BNT-level data for the produced nonzero-sector
families, with whatever total dimensions support the proportional-decomposition
data. The conversion from BNT-cover hypotheses to common primitive phase-cover
hypotheses then lets the common-phase-cover theorem supply the overlap-span data. -/
theorem sectorBasisOverlapSpanHypotheses_of_reindexedNonzeroParts_bntCover
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
    ∃ p : ℕ, 0 < p ∧
    ∃ P Q : SectorDecomposition (blockPhysDim d p),
      SameMPV₂ P.toTensor Q.toTensor ∧
      HasBNTSectorData P ∧ HasBNTSectorData Q ∧
      SectorBasisOverlapSpanHypotheses P Q := by
  refine sectorBasisOverlapSpanHypotheses_of_reindexedNonzeroParts_commonPhaseCover
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

/-- **Sector basis overlap-span data via a BNT proportional-decomposition comparison.**

This is the proportional-comparison variant of
`sectorBasisOverlapSpanHypotheses_of_reindexedNonzeroParts`. A BNT proportional-decomposition
conclusion for the two nonzero-weight block families gives a common MPV phase cover, hence the
finite-length span equality needed by the collapsed BNT representative construction. -/
theorem sectorBasisOverlapSpanHypotheses_of_reindexedNonzeroParts_proportional
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
    ∃ p : ℕ, 0 < p ∧
    ∃ P Q : SectorDecomposition (blockPhysDim d p),
      SameMPV₂ P.toTensor Q.toTensor ∧
      HasBNTSectorData P ∧ HasBNTSectorData Q ∧
      SectorBasisOverlapSpanHypotheses P Q := by
  obtain ⟨p, hp, zeroTailA, zeroTailB, rA, dimA, μA, blocksA,
      rB, dimB, μB, blocksB, hAblocks, hBblocks, hAPos, hBPos, hNonzeroPos,
      hZero, hμA, hμB, hTPA, hTPB, hPrimA, hPrimB, hIrrA, hIrrB, hDimA, hDimB⟩ :=
    afterBlocking_commonPrimitiveIrreducibleBlocks_of_reindexedNonzeroParts A B hSame hReindexed
  have hHyp : CommonPrimitiveProportionalHypotheses zeroTailA zeroTailB blocksA blocksB :=
    hRemaining hp hAblocks hBblocks hAPos hBPos hNonzeroPos hZero hμA hμB hTPA hTPB
      hPrimA hPrimB hIrrA hIrrB hDimA hDimB
  have hSpanHyp : CommonPrimitiveSpanHypotheses zeroTailA zeroTailB blocksA blocksB :=
    hHyp.toSpanHypotheses
  letI : ∀ x : Fin rA, NeZero (dimA x) := fun x => ⟨Nat.ne_of_gt (hDimA x)⟩
  letI : ∀ x : Fin rB, NeZero (dimB x) := fun x => ⟨Nat.ne_of_gt (hDimB x)⟩
  let nonzeroA := toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA
  let nonzeroB := toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB
  have hAB : SameMPV₂ (blockTensor (d := d) (D := D₁) A p)
                      (blockTensor (d := d) (D := D₂) B p) :=
    sameMPV₂_blockTensor A B hSame p
  have hNonzero : SameMPV₂ nonzeroA nonzeroB :=
    sameMPV₂_live_of_sameMPV₂_with_zeroTail_eq
      (blockTensor (d := d) (D := D₁) A p)
      (blockTensor (d := d) (D := D₂) B p)
      nonzeroA nonzeroB hAB hAblocks hBblocks hSpanHyp.zeroTail_eq
  obtain ⟨P, Q, hPblocks, hQblocks, hPbnt, hQbnt, hOverlapSpan⟩ :=
    exists_bnt_sectorDecomp_pair_with_overlapSpan_of_block_span_eq
      (d := blockPhysDim d p) μA blocksA μB blocksB hTPA hTPB hIrrA hIrrB
      hPrimA hPrimB hSpanHyp.left_injective hSpanHyp.right_injective hμA hμB hSpanHyp.span_eq
  have hPQeq : SameMPV₂ P.toTensor Q.toTensor := by
    intro N σ
    calc
      mpv P.toTensor σ = mpv nonzeroA σ := hPblocks N σ
      _ = mpv nonzeroB σ := hNonzero N σ
      _ = mpv Q.toTensor σ := (hQblocks N σ).symm
  exact ⟨p, hp, P, Q, hPQeq, hPbnt, hQbnt, hOverlapSpan⟩


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

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.Assembly.StructuralTheorem
import TNLean.MPS.CanonicalForm.Assembly.SectorComparisonCore

open scoped Matrix BigOperators ComplexOrder MatrixOrder

/-!
# Common primitive proportional data

This file records the span, phase-cover, proportional-comparison, and BNT-cover
hypotheses for common primitive nonzero-sector families.  These structures express
the remaining data needed to pass from the common-sector structural theorem to
the BNT overlap-rigidity comparison.

The zero-tail dimensions below are the total bond dimensions of the separated
all-zero leftover blocks.  They are the dimension gaps allowed by
`∑ k, D_k ≤ D`, where the remaining summands are zero blocks.

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
lemma of_commonPhaseCover
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
  /-- The two nonzero-sector block families carry a common MPV phase cover. -/
  cover : Nonempty (MPVCommonPhaseCover blocksA blocksB)

namespace CommonPrimitivePhaseCoverHypotheses

/-- A common MPV phase cover hypothesis implies the corresponding span hypothesis. -/
lemma toSpanHypotheses
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
lemma toPhaseCoverHypotheses
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
lemma toSpanHypotheses
    {d p rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {zeroTailA zeroTailB : ℕ}
    {blocksA : (x : Fin rA) → MPSTensor (blockPhysDim d p) (dimA x)}
    {blocksB : (x : Fin rB) → MPSTensor (blockPhysDim d p) (dimB x)}
    (h : CommonPrimitiveProportionalHypotheses zeroTailA zeroTailB blocksA blocksB) :
    CommonPrimitiveSpanHypotheses zeroTailA zeroTailB blocksA blocksB :=
  h.toPhaseCoverHypotheses.toSpanHypotheses

end CommonPrimitiveProportionalHypotheses

/-! ### Zero-tail equality from proportional block matching -/

/-- At length zero, a block-diagonal tensor contributes the sum of the block dimensions. -/
private theorem mpv_toTensorFromBlocks_zero_eq_sum_dim
    {d r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (blocks : (x : Fin r) → MPSTensor d (dim x))
    (σ : Fin 0 → Fin d) :
    mpv (toTensorFromBlocks (d := d) (μ := μ) blocks) σ =
      ∑ x : Fin r, (dim x : ℂ) := by
  rw [mpv_toTensorFromBlocks_eq_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [mpv, coeff, Matrix.trace_one]

/-- A proportional-decomposition matching identifies the total nonzero bond dimensions. -/
private theorem sum_dim_eq_of_proportionalDecompositionConclusion
    {d rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {blocksA : (x : Fin rA) → MPSTensor d (dimA x)}
    {blocksB : (x : Fin rB) → MPSTensor d (dimB x)}
    (hMatch : ProportionalDecompositionConclusion (d := d) blocksA blocksB) :
    (∑ x : Fin rA, (dimA x : ℂ)) = ∑ y : Fin rB, (dimB y : ℂ) := by
  rcases hMatch with ⟨_, perm, hmatch⟩
  calc
    (∑ x : Fin rA, (dimA x : ℂ)) =
        ∑ x : Fin rA, (dimB (perm x) : ℂ) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          obtain ⟨hdim, _⟩ := hmatch x
          simp [hdim]
    _ = ∑ y : Fin rB, (dimB y : ℂ) := by
          let f : Fin rA → ℂ := fun x => (dimB (perm x) : ℂ)
          let g : Fin rB → ℂ := fun y => (dimB y : ℂ)
          have hfg : ∀ x, f x = g (perm x) := fun _ => rfl
          simpa [f, g] using (Fintype.sum_equiv perm f g hfg)

/-- The length-zero identity and proportional block matching force equal zero-tail dimensions.

The structural theorem already supplies the length-zero equation for the two zero-tail plus
nonzero-sector decompositions. A proportional-decomposition conclusion matches the nonzero
blocks by a permutation with equal bond dimensions, so the nonzero length-zero contributions
cancel. -/
theorem zeroTail_eq_of_proportionalDecompositionConclusion
    {d rA rB zeroTailA zeroTailB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    {blocksA : (x : Fin rA) → MPSTensor d (dimA x)}
    {blocksB : (x : Fin rB) → MPSTensor d (dimB x)}
    (hZero : ∀ σ : Fin 0 → Fin d,
      (zeroTailA : ℂ) + mpv (toTensorFromBlocks (d := d) (μ := μA) blocksA) σ =
        (zeroTailB : ℂ) + mpv (toTensorFromBlocks (d := d) (μ := μB) blocksB) σ)
    (hMatch : ProportionalDecompositionConclusion (d := d) blocksA blocksB) :
    zeroTailA = zeroTailB := by
  let σ : Fin 0 → Fin d := Fin.elim0
  have hsum :=
    sum_dim_eq_of_proportionalDecompositionConclusion
      (d := d) (blocksA := blocksA) (blocksB := blocksB) hMatch
  have hzero := hZero σ
  rw [mpv_toTensorFromBlocks_zero_eq_sum_dim μA blocksA σ,
    mpv_toTensorFromBlocks_zero_eq_sum_dim μB blocksB σ] at hzero
  have hzero' :
      (zeroTailA : ℂ) + ∑ y : Fin rB, (dimB y : ℂ) =
        (zeroTailB : ℂ) + ∑ y : Fin rB, (dimB y : ℂ) := by
    simpa [hsum] using hzero
  exact (Nat.cast_injective (R := ℂ)) (add_right_cancel hzero')

/-- Remaining BNT-level inputs for constructing a common MPV phase cover
from the common-length cyclic sector families produced by the structural theorem.

The structural theorem
`afterBlocking_commonPrimitiveIrreducibleBlocks_of_reindexedNonzeroParts`
supplies trace-preserving, primitive, tensor-irreducible block families
with nonzero weights and positive bond dimensions at a common blocking
length.  The fields below record the additional BNT hypotheses needed
to compare the two families and obtain a common MPV phase cover.

For non-periodic tensors, the comparison is applied after choosing one
representative for each group of common cyclic sectors with the same transported
weight. On that representative family one can impose strict ordering, BNT
separation, and proportional block matching without confusing sectors that
belong to the same original block. -/
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

/-- BNT-cover inputs for representative common-sector families.

The common cyclic-sector family can contain several sectors from the same original block with
the same transported weight.  This structure collects the representative-sector hypotheses:
one representative per original nonzero block, strict ordering of the representative weights,
BNT separation among representatives, the length-zero identity for the representative nonzero
parts, one-site injectivity, and proportional decomposition data for the two representative
families. -/
structure CommonRepresentativeBNTCoverHypotheses
    {d p rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {blocksA : (k : Fin rA) → MPSTensor d (dimA k)}
    {blocksB : (k : Fin rB) → MPSTensor d (dimB k)}
    (FA : CommonBlockedCyclicSectorFamily blocksA)
    (FB : CommonBlockedCyclicSectorFamily blocksB)
    (hpA : FA.p = p) (hpB : FB.p = p)
    [∀ k, NeZero (FA.commonRepresentativeDim k)]
    [∀ k, NeZero (FB.commonRepresentativeDim k)]
    {zeroTailA zeroTailB DtotA DtotB : ℕ}
    (μA : Fin rA → ℂ) (μB : Fin rB → ℂ) : Type where
  /-- The original left nonzero-sector weights are nonzero. -/
  left_weight_ne_zero : ∀ k, μA k ≠ 0
  /-- The original right nonzero-sector weights are nonzero. -/
  right_weight_ne_zero : ∀ k, μB k ≠ 0
  /-- The transported left representative weights are strictly ordered by norm. -/
  left_weight_strict_anti :
    StrictAnti (fun k : Fin rA => ‖FA.commonRepresentativeWeight μA k‖)
  /-- The transported right representative weights are strictly ordered by norm. -/
  right_weight_strict_anti :
    StrictAnti (fun k : Fin rB => ‖FB.commonRepresentativeWeight μB k‖)
  /-- Distinct left representatives are not gauge-phase equivalent. -/
  notGpeA :
    BlocksNotGaugePhaseEquiv (d := blockPhysDim d p) (FA.commonRepresentativeBlocksAt hpA)
  /-- Distinct right representatives are not gauge-phase equivalent. -/
  notGpeB :
    BlocksNotGaugePhaseEquiv (d := blockPhysDim d p) (FB.commonRepresentativeBlocksAt hpB)
  /-- The length-zero identity for the representative nonzero parts. -/
  zero_length_identity : ∀ σ : Fin 0 → Fin (blockPhysDim d p),
    (zeroTailA : ℂ) +
        mpv (toTensorFromBlocks (d := blockPhysDim d p)
          (μ := FA.commonRepresentativeWeight μA) (FA.commonRepresentativeBlocksAt hpA)) σ =
      (zeroTailB : ℂ) +
        mpv (toTensorFromBlocks (d := blockPhysDim d p)
          (μ := FB.commonRepresentativeWeight μB) (FB.commonRepresentativeBlocksAt hpB)) σ
  /-- The left representative common-sector blocks are one-site injective. -/
  left_injective : ∀ k, IsInjective (FA.commonRepresentativeBlocksAt hpA k)
  /-- The right representative common-sector blocks are one-site injective. -/
  right_injective : ∀ k, IsInjective (FB.commonRepresentativeBlocksAt hpB k)
  /-- Proportional decomposition data linking the two representative families. -/
  decompData : ProportionalDecompositionData (d := blockPhysDim d p)
    (FA.commonRepresentativeBlocksAt hpA)
    (FB.commonRepresentativeBlocksAt hpB) DtotA DtotB

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

/-- Form `CommonPrimitiveBNTCoverHypotheses` from common primitive structural data,
deriving zero-tail equality from the length-zero identity and the BNT proportional
matching. -/
def ofCommonPrimitiveData_zeroTailIdentity
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
    (hZero : ∀ σ : Fin 0 → Fin (blockPhysDim d p),
      (zeroTailA : ℂ) + mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) σ =
        (zeroTailB : ℂ) +
          mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) σ)
    (hInjA : ∀ x, IsInjective (blocksA x))
    (hInjB : ∀ x, IsInjective (blocksB x))
    (hDecomp : ProportionalDecompositionData (d := blockPhysDim d p)
      blocksA blocksB DtotA DtotB) :
    CommonPrimitiveBNTCoverHypotheses (zeroTailA := zeroTailA) (zeroTailB := zeroTailB)
      (DtotA := DtotA) (DtotB := DtotB) μA μB blocksA blocksB := by
  have hDimA : ∀ x, 0 < dimA x := fun x => Nat.pos_of_ne_zero (NeZero.ne (dimA x))
  have hDimB : ∀ x, 0 < dimB x := fun x => Nat.pos_of_ne_zero (NeZero.ne (dimB x))
  have hNcfA : IsNormalCanonicalForm (d := blockPhysDim d p) μA blocksA :=
    isNormalCanonicalForm_of_tp_primitive_irr_sorted
      (d' := blockPhysDim d p) (μ := μA) blocksA hTPA hPrimA hDimA hμA hIrrA hAntiA
  have hNcfB : IsNormalCanonicalForm (d := blockPhysDim d p) μB blocksB :=
    isNormalCanonicalForm_of_tp_primitive_irr_sorted
      (d' := blockPhysDim d p) (μ := μB) blocksB hTPB hPrimB hDimB hμB hIrrB hAntiB
  have hMatch : ProportionalDecompositionConclusion (d := blockPhysDim d p) blocksA blocksB :=
    fundamentalTheorem_of_separated_normalCFBNT_data
      blocksA blocksB hNcfA hNotGpeA hNcfB hNotGpeB hDecomp
  exact ofCommonPrimitiveData hμA hμB hTPA hTPB hPrimA hPrimB hIrrA hIrrB
    hAntiA hAntiB hNotGpeA hNotGpeB
    (zeroTail_eq_of_proportionalDecompositionConclusion hZero hMatch) hInjA hInjB hDecomp

/-- Form `CommonPrimitiveBNTCoverHypotheses` from normal-CF-BNT data and the remaining
zero-tail, injectivity, and proportional-decomposition inputs. -/
def ofNormalCanonicalFormBNT
    {d p rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {zeroTailA zeroTailB DtotA DtotB : ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    {blocksA : (x : Fin rA) → MPSTensor (blockPhysDim d p) (dimA x)}
    {blocksB : (x : Fin rB) → MPSTensor (blockPhysDim d p) (dimB x)}
    (hA : IsNormalCanonicalFormBNT (d := blockPhysDim d p) μA blocksA)
    (hB : IsNormalCanonicalFormBNT (d := blockPhysDim d p) μB blocksB)
    (hZeroTail : zeroTailA = zeroTailB)
    (hInjA : ∀ x, IsInjective (blocksA x))
    (hInjB : ∀ x, IsInjective (blocksB x))
    (hDecomp : ProportionalDecompositionData (d := blockPhysDim d p)
      blocksA blocksB DtotA DtotB) :
    CommonPrimitiveBNTCoverHypotheses (zeroTailA := zeroTailA) (zeroTailB := zeroTailB)
      (DtotA := DtotA) (DtotB := DtotB) μA μB blocksA blocksB where
  ncfA := hA.toIsNormalCanonicalForm
  ncfB := hB.toIsNormalCanonicalForm
  notGpeA := hA.blocks_not_equiv
  notGpeB := hB.blocks_not_equiv
  zeroTail_eq := hZeroTail
  left_injective := hInjA
  right_injective := hInjB
  decompData := hDecomp

/-- Form `CommonPrimitiveBNTCoverHypotheses` from normal-CF-BNT data, deriving zero-tail
equality from the length-zero identity and the proportional BNT comparison. -/
def ofNormalCanonicalFormBNT_zeroTailIdentity
    {d p rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {zeroTailA zeroTailB DtotA DtotB : ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    {blocksA : (x : Fin rA) → MPSTensor (blockPhysDim d p) (dimA x)}
    {blocksB : (x : Fin rB) → MPSTensor (blockPhysDim d p) (dimB x)}
    (hA : IsNormalCanonicalFormBNT (d := blockPhysDim d p) μA blocksA)
    (hB : IsNormalCanonicalFormBNT (d := blockPhysDim d p) μB blocksB)
    (hZero : ∀ σ : Fin 0 → Fin (blockPhysDim d p),
      (zeroTailA : ℂ) + mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) σ =
        (zeroTailB : ℂ) +
          mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) σ)
    (hInjA : ∀ x, IsInjective (blocksA x))
    (hInjB : ∀ x, IsInjective (blocksB x))
    (hDecomp : ProportionalDecompositionData (d := blockPhysDim d p)
      blocksA blocksB DtotA DtotB) :
    CommonPrimitiveBNTCoverHypotheses (zeroTailA := zeroTailA) (zeroTailB := zeroTailB)
      (DtotA := DtotA) (DtotB := DtotB) μA μB blocksA blocksB := by
  have hMatch : ProportionalDecompositionConclusion (d := blockPhysDim d p) blocksA blocksB :=
    fundamentalTheorem_of_separated_normalCFBNT_data
      blocksA blocksB
      hA.toIsNormalCanonicalForm hA.blocks_not_equiv
      hB.toIsNormalCanonicalForm hB.blocks_not_equiv
      hDecomp
  exact ofNormalCanonicalFormBNT hA hB
    (zeroTail_eq_of_proportionalDecompositionConclusion hZero hMatch) hInjA hInjB hDecomp

/-- Representative common-sector families give the BNT-cover hypotheses once the
representative weights are strictly ordered, representatives are BNT-separated, and the
remaining zero-tail, injectivity, and proportional-decomposition inputs are supplied. -/
noncomputable def ofCommonRepresentatives_zeroTailIdentity
    {d p rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {blocksA : (k : Fin rA) → MPSTensor d (dimA k)}
    {blocksB : (k : Fin rB) → MPSTensor d (dimB k)}
    (FA : CommonBlockedCyclicSectorFamily blocksA)
    (FB : CommonBlockedCyclicSectorFamily blocksB)
    (hpA : FA.p = p) (hpB : FB.p = p)
    [∀ k, NeZero (FA.commonRepresentativeDim k)]
    [∀ k, NeZero (FB.commonRepresentativeDim k)]
    {zeroTailA zeroTailB DtotA DtotB : ℕ}
    (μA : Fin rA → ℂ) (μB : Fin rB → ℂ)
    (hμA : ∀ k, μA k ≠ 0)
    (hμB : ∀ k, μB k ≠ 0)
    (hAntiA : StrictAnti (fun k : Fin rA => ‖FA.commonRepresentativeWeight μA k‖))
    (hAntiB : StrictAnti (fun k : Fin rB => ‖FB.commonRepresentativeWeight μB k‖))
    (hNotGpeA : BlocksNotGaugePhaseEquiv (d := blockPhysDim d p)
      (FA.commonRepresentativeBlocksAt hpA))
    (hNotGpeB : BlocksNotGaugePhaseEquiv (d := blockPhysDim d p)
      (FB.commonRepresentativeBlocksAt hpB))
    (hZero : ∀ σ : Fin 0 → Fin (blockPhysDim d p),
      (zeroTailA : ℂ) +
          mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := FA.commonRepresentativeWeight μA)
            (FA.commonRepresentativeBlocksAt hpA)) σ =
        (zeroTailB : ℂ) +
          mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := FB.commonRepresentativeWeight μB)
            (FB.commonRepresentativeBlocksAt hpB)) σ)
    (hInjA : ∀ k, IsInjective
      (FA.commonRepresentativeBlocksAt hpA k))
    (hInjB : ∀ k, IsInjective
      (FB.commonRepresentativeBlocksAt hpB k))
    (hDecomp : ProportionalDecompositionData (d := blockPhysDim d p)
      (FA.commonRepresentativeBlocksAt hpA)
      (FB.commonRepresentativeBlocksAt hpB) DtotA DtotB) :
    CommonPrimitiveBNTCoverHypotheses (zeroTailA := zeroTailA) (zeroTailB := zeroTailB)
      (DtotA := DtotA) (DtotB := DtotB)
      (FA.commonRepresentativeWeight μA) (FB.commonRepresentativeWeight μB)
      (FA.commonRepresentativeBlocksAt hpA)
      (FB.commonRepresentativeBlocksAt hpB) := by
  exact ofNormalCanonicalFormBNT_zeroTailIdentity
    (isNormalCanonicalFormBNT_commonRepresentativeBlocksAt
      FA hpA μA hμA hAntiA hNotGpeA)
    (isNormalCanonicalFormBNT_commonRepresentativeBlocksAt
      FB hpB μB hμB hAntiB hNotGpeB)
    hZero hInjA hInjB hDecomp

/-- Representative BNT-cover data convert to the primitive BNT-cover hypotheses for the
representative common-sector families. -/
noncomputable def ofCommonRepresentativeBNTCoverHypotheses
    {d p rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {blocksA : (k : Fin rA) → MPSTensor d (dimA k)}
    {blocksB : (k : Fin rB) → MPSTensor d (dimB k)}
    (FA : CommonBlockedCyclicSectorFamily blocksA)
    (FB : CommonBlockedCyclicSectorFamily blocksB)
    (hpA : FA.p = p) (hpB : FB.p = p)
    [∀ k, NeZero (FA.commonRepresentativeDim k)]
    [∀ k, NeZero (FB.commonRepresentativeDim k)]
    {zeroTailA zeroTailB DtotA DtotB : ℕ}
    (μA : Fin rA → ℂ) (μB : Fin rB → ℂ)
    (h : CommonRepresentativeBNTCoverHypotheses (zeroTailA := zeroTailA)
      (zeroTailB := zeroTailB) (DtotA := DtotA) (DtotB := DtotB)
      FA FB hpA hpB μA μB) :
    CommonPrimitiveBNTCoverHypotheses (zeroTailA := zeroTailA) (zeroTailB := zeroTailB)
      (DtotA := DtotA) (DtotB := DtotB)
      (FA.commonRepresentativeWeight μA) (FB.commonRepresentativeWeight μB)
      (FA.commonRepresentativeBlocksAt hpA)
      (FB.commonRepresentativeBlocksAt hpB) :=
  ofCommonRepresentatives_zeroTailIdentity
    FA FB hpA hpB μA μB
    h.left_weight_ne_zero h.right_weight_ne_zero
    h.left_weight_strict_anti h.right_weight_strict_anti
    h.notGpeA h.notGpeB
    h.zero_length_identity h.left_injective h.right_injective h.decompData

/-- BNT-cover hypotheses produce a common MPV phase cover. -/
lemma toMPVCommonPhaseCover
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

/-- BNT-cover hypotheses produce the common primitive phase-cover hypotheses. -/
lemma toCommonPrimitivePhaseCoverHypotheses
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


end MPSTensor

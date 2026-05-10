/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.SectorComparison.StructuralTheorem
import TNLean.MPS.CanonicalForm.PhaseCover
import TNLean.MPS.FundamentalTheorem.Multi

open scoped Matrix BigOperators ComplexOrder MatrixOrder

/-!
# Common primitive proportional data

This file records the span, phase-cover, proportional-decomposition, and BNT
comparison hypotheses for common primitive nonzero-sector families.  These structures
express the remaining hypotheses needed to pass from the common-sector structural
theorem to the BNT overlap-rigidity comparison.

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
and equality of their finite-length MPV spans.

This structure is a deliberate parameterization — the lightest boundary that collects the
span-level inputs needed to proceed from the structural theorem to the BNT overlap-rigidity
comparison.  It records the decomposition of arXiv:1606.00608, Section II, lines 283–302
where the block families and their MPV spans are matched after the canonical-form reduction.
When the BNT-cover data in `CommonPrimitiveBNTCoverHypotheses` have been discharged
(tracker #1498, sub-issue #1501), this structure is automatically satisfied via
`toSpanHypotheses`. -/
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

This is the common phase-cover variant of `CommonPrimitiveSpanHypotheses`: the structural
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
BNT comparison conclusion for the two block families.

This structure is a deliberate parameterization.  It records the proportional Fundamental
Theorem conclusion (arXiv:1606.00608, Theorem II.1, lines 283–352): after the
block-injective span is established, the two block families are compared by a permutation
of the BNT representatives with equal dimensions.  The `proportional` field records that
conclusion; the remaining fields (`zeroTail_eq`, injectivity) ensure the dimensions are
compatible.  Once the BNT-cover data in `CommonPrimitiveBNTCoverHypotheses` are discharged
(tracker #1498, sub-issue #1501), this structure follows from
`fundamentalTheorem_of_separated_normalCFBNT_data`. -/
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

/-- A positive arithmetic subsequence of a convergent power sequence has the same limit. -/
theorem tendsto_blockPowerCoeff_of_tendsto_pow
    {μ a : ℂ} {L : ℕ} (hL : 0 < L)
    (h : Filter.Tendsto (fun N : ℕ => μ ^ N) Filter.atTop (nhds a)) :
    Filter.Tendsto (fun N : ℕ => (μ ^ L) ^ N) Filter.atTop (nhds a) := by
  have hMul : Filter.Tendsto (fun N : ℕ => L * N) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b =>
      ⟨b, fun N hN => le_trans hN (Nat.le_mul_of_pos_left N hL)⟩
  simpa [Function.comp, ← pow_mul] using h.comp hMul

namespace CommonPrimitiveBNTCoverHypotheses

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
      (zeroTailA : ℂ) +
          mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) σ =
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

/-- Construct `ProportionalDecompositionData` for two assembled block-diagonal tensor
families with the same MPV family, once the block-weight power coefficient families
have specified nonzero limits.

The block-diagonal MPV expansion has coefficients `(μA j) ^ N` and `(μB k) ^ N` at
length `N`, as in `mpv_toTensorFromBlocks_eq_sum`.  Therefore this construction keeps
the required coefficient convergence as an explicit input; it does not replace the
spectral/power-sum comparison needed to obtain such nonzero limits in the general
BNT setting.  The proportionality ratio is identically `1`, supplied by `SameMPV₂`.

This construction is formal in the block families and does not use normal-CF-BNT
hypotheses; callers add those hypotheses when assembling `CommonPrimitiveBNTCoverHypotheses`. -/
noncomputable def proportionalDecompositionData_of_sameMPV_toTensorFromBlocks
    {d rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (blocksA : (j : Fin rA) → MPSTensor d (dimA j))
    (blocksB : (k : Fin rB) → MPSTensor d (dimB k))
    (aLim : Fin rA → ℂ) (bLim : Fin rB → ℂ)
    (haCoeff : ∀ j, Filter.Tendsto (fun N : ℕ => (μA j) ^ N) Filter.atTop (nhds (aLim j)))
    (hbCoeff : ∀ k, Filter.Tendsto (fun N : ℕ => (μB k) ^ N) Filter.atTop (nhds (bLim k)))
    (haLim_ne : ∀ j, aLim j ≠ 0) (hbLim_ne : ∀ k, bLim k ≠ 0)
    (hSame : SameMPV₂
      (toTensorFromBlocks (d := d) (μ := μA) blocksA)
      (toTensorFromBlocks (d := d) (μ := μB) blocksB)) :
    ProportionalDecompositionData (d := d) blocksA blocksB
      (∑ j : Fin rA, dimA j) (∑ k : Fin rB, dimB k) where
  A_total := toTensorFromBlocks (d := d) (μ := μA) blocksA
  B_total := toTensorFromBlocks (d := d) (μ := μB) blocksB
  aCoeff := fun N j => (μA j) ^ N
  bCoeff := fun N k => (μB k) ^ N
  aLim := aLim
  bLim := bLim
  c := fun _ => 1
  cLim := 1
  hA_decomp := fun _ σ => by
    simpa [smul_eq_mul] using mpv_toTensorFromBlocks_eq_sum (d := d) μA blocksA σ
  hB_decomp := fun _ σ => by
    simpa [smul_eq_mul] using mpv_toTensorFromBlocks_eq_sum (d := d) μB blocksB σ
  haCoeff := haCoeff
  hbCoeff := hbCoeff
  haLim_ne := haLim_ne
  hbLim_ne := hbLim_ne
  hProp := fun N σ => by
    rw [one_mul]
    exact hSame N σ
  hc := tendsto_const_nhds
  hcLim_ne := one_ne_zero

/-- Form `CommonPrimitiveBNTCoverHypotheses` from normal-CF-BNT data and same MPVs of the
assembled block-diagonal tensors.

The block-diagonal MPV expansion has coefficient families `(μA j) ^ N` and `(μB k) ^ N`.
Accordingly the convergence and nonzero-limit data for those power families remain explicit
inputs; the `SameMPV₂` hypothesis supplies only the proportionality field with ratio `1`.
The length-zero identity is used, as in `ofNormalCanonicalFormBNT_zeroTailIdentity`, to derive
zero-tail equality after applying the proportional BNT comparison. -/
noncomputable def ofNormalCanonicalFormBNT_sameMPV_toTensorFromBlocks_zeroTailIdentity
    {d p rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {zeroTailA zeroTailB : ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    {blocksA : (x : Fin rA) → MPSTensor (blockPhysDim d p) (dimA x)}
    {blocksB : (x : Fin rB) → MPSTensor (blockPhysDim d p) (dimB x)}
    (hA : IsNormalCanonicalFormBNT (d := blockPhysDim d p) μA blocksA)
    (hB : IsNormalCanonicalFormBNT (d := blockPhysDim d p) μB blocksB)
    (aLim : Fin rA → ℂ) (bLim : Fin rB → ℂ)
    (haCoeff : ∀ j,
      Filter.Tendsto (fun N : ℕ => (μA j) ^ N) Filter.atTop (nhds (aLim j)))
    (hbCoeff : ∀ k,
      Filter.Tendsto (fun N : ℕ => (μB k) ^ N) Filter.atTop (nhds (bLim k)))
    (haLim_ne : ∀ j, aLim j ≠ 0) (hbLim_ne : ∀ k, bLim k ≠ 0)
    (hSame : SameMPV₂
      (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA)
      (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB))
    (hZero : ∀ σ : Fin 0 → Fin (blockPhysDim d p),
      (zeroTailA : ℂ) +
          mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μA) blocksA) σ =
        (zeroTailB : ℂ) +
          mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μB) blocksB) σ)
    (hInjA : ∀ x, IsInjective (blocksA x))
    (hInjB : ∀ x, IsInjective (blocksB x)) :
    CommonPrimitiveBNTCoverHypotheses (zeroTailA := zeroTailA) (zeroTailB := zeroTailB)
      (DtotA := ∑ j : Fin rA, dimA j) (DtotB := ∑ k : Fin rB, dimB k)
      μA μB blocksA blocksB := by
  exact ofNormalCanonicalFormBNT_zeroTailIdentity hA hB hZero hInjA hInjB
    (proportionalDecompositionData_of_sameMPV_toTensorFromBlocks
      (d := blockPhysDim d p) (μA := μA) (μB := μB)
      blocksA blocksB aLim bLim haCoeff hbCoeff haLim_ne hbLim_ne hSame)

/-- BNT-cover hypotheses after a fixed positive reblocking.

Starting from unblocked normal-CF-BNT hypotheses, a positive common blocking length `L`,
explicit blocked BNT-separation, and one-site injectivity of the blocked blocks,
this transports the normal-form, MPV-equality, zero-length, and coefficient-limit
conditions and yields `CommonPrimitiveBNTCoverHypotheses` at blocking period `L`. -/
noncomputable def ofNormalCanonicalFormBNT_sameMPV_toTensorFromBlocks_zeroTailIdentity_blockPower
    {d rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ j, NeZero (dimA j)] [∀ k, NeZero (dimB k)]
    {zeroTailA zeroTailB : ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    {blocksA : (j : Fin rA) → MPSTensor d (dimA j)}
    {blocksB : (k : Fin rB) → MPSTensor d (dimB k)}
    (hA : IsNormalCanonicalFormBNT (d := d) μA blocksA)
    (hB : IsNormalCanonicalFormBNT (d := d) μB blocksB)
    (L : ℕ) (hL : 0 < L)
    (aLim : Fin rA → ℂ) (bLim : Fin rB → ℂ)
    (haCoeff : ∀ j,
      Filter.Tendsto (fun N : ℕ => (μA j) ^ N) Filter.atTop (nhds (aLim j)))
    (hbCoeff : ∀ k,
      Filter.Tendsto (fun N : ℕ => (μB k) ^ N) Filter.atTop (nhds (bLim k)))
    (haLim_ne : ∀ j, aLim j ≠ 0) (hbLim_ne : ∀ k, bLim k ≠ 0)
    (hSame : SameMPV₂
      (toTensorFromBlocks (d := d) (μ := μA) blocksA)
      (toTensorFromBlocks (d := d) (μ := μB) blocksB))
    (hZero : ∀ σ : Fin 0 → Fin d,
      (zeroTailA : ℂ) +
          mpv (toTensorFromBlocks (d := d) (μ := μA) blocksA) σ =
        (zeroTailB : ℂ) +
          mpv (toTensorFromBlocks (d := d) (μ := μB) blocksB) σ)
    (hNotGpeA : BlocksNotGaugePhaseEquiv (d := blockPhysDim d L)
      (fun j => blockTensor (d := d) (D := dimA j) (blocksA j) L))
    (hNotGpeB : BlocksNotGaugePhaseEquiv (d := blockPhysDim d L)
      (fun k => blockTensor (d := d) (D := dimB k) (blocksB k) L))
    (hInjA : ∀ j, IsInjective (blockTensor (d := d) (D := dimA j) (blocksA j) L))
    (hInjB : ∀ k, IsInjective (blockTensor (d := d) (D := dimB k) (blocksB k) L)) :
    CommonPrimitiveBNTCoverHypotheses (d := d) (p := L)
      (zeroTailA := zeroTailA) (zeroTailB := zeroTailB)
      (DtotA := ∑ j : Fin rA, dimA j) (DtotB := ∑ k : Fin rB, dimB k)
      (fun j => (μA j) ^ L) (fun k => (μB k) ^ L)
      (fun j => blockTensor (d := d) (D := dimA j) (blocksA j) L)
      (fun k => blockTensor (d := d) (D := dimB k) (blocksB k) L) := by
  exact ofNormalCanonicalFormBNT_sameMPV_toTensorFromBlocks_zeroTailIdentity
    (d := d) (p := L)
    (μA := fun j => (μA j) ^ L) (μB := fun k => (μB k) ^ L)
    (blocksA := fun j => blockTensor (d := d) (D := dimA j) (blocksA j) L)
    (blocksB := fun k => blockTensor (d := d) (D := dimB k) (blocksB k) L)
    (IsNormalCanonicalFormBNT.blockTensor_of_notGpe hA hL hNotGpeA)
    (IsNormalCanonicalFormBNT.blockTensor_of_notGpe hB hL hNotGpeB)
    aLim bLim
    (fun j => MPSTensor.tendsto_blockPowerCoeff_of_tendsto_pow hL (haCoeff j))
    (fun k => MPSTensor.tendsto_blockPowerCoeff_of_tendsto_pow hL (hbCoeff k))
    haLim_ne hbLim_ne
    (sameMPV₂_toTensorFromBlocks_blockPower
      (d := d) μA blocksA μB blocksB hSame L)
    (zeroTail_identity_toTensorFromBlocks_blockPower
      (d := d) μA blocksA μB blocksB hZero)
    hInjA hInjB

/-- Common-injective reblocking statement for the same-MPV/`toTensorFromBlocks` construction.

The common positive blocking length and one-site injectivity hypotheses are supplied by
`exists_common_blockTensor_isInjective_two_of_isNormalCanonicalFormBNT`.  Blocked
BNT separation and the power-limit hypotheses remain explicit inputs.  The returned value
bundles the chosen positive blocking length together with the corresponding
`CommonPrimitiveBNTCoverHypotheses`. -/
noncomputable def
    exists_commonInjectiveBlock_ofNormalCanonicalFormBNT_sameMPV_toTensorFromBlocks_zeroTailIdentity
    {d rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ j, NeZero (dimA j)] [∀ k, NeZero (dimB k)]
    {zeroTailA zeroTailB : ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    {blocksA : (j : Fin rA) → MPSTensor d (dimA j)}
    {blocksB : (k : Fin rB) → MPSTensor d (dimB k)}
    (hA : IsNormalCanonicalFormBNT (d := d) μA blocksA)
    (hB : IsNormalCanonicalFormBNT (d := d) μB blocksB)
    (aLim : Fin rA → ℂ) (bLim : Fin rB → ℂ)
    (haCoeff : ∀ j,
      Filter.Tendsto (fun N : ℕ => (μA j) ^ N) Filter.atTop (nhds (aLim j)))
    (hbCoeff : ∀ k,
      Filter.Tendsto (fun N : ℕ => (μB k) ^ N) Filter.atTop (nhds (bLim k)))
    (haLim_ne : ∀ j, aLim j ≠ 0) (hbLim_ne : ∀ k, bLim k ≠ 0)
    (hSame : SameMPV₂
      (toTensorFromBlocks (d := d) (μ := μA) blocksA)
      (toTensorFromBlocks (d := d) (μ := μB) blocksB))
    (hZero : ∀ σ : Fin 0 → Fin d,
      (zeroTailA : ℂ) +
          mpv (toTensorFromBlocks (d := d) (μ := μA) blocksA) σ =
        (zeroTailB : ℂ) +
          mpv (toTensorFromBlocks (d := d) (μ := μB) blocksB) σ)
    (hNotGpeA : ∀ L, 0 < L → BlocksNotGaugePhaseEquiv (d := blockPhysDim d L)
      (fun j => blockTensor (d := d) (D := dimA j) (blocksA j) L))
    (hNotGpeB : ∀ L, 0 < L → BlocksNotGaugePhaseEquiv (d := blockPhysDim d L)
      (fun k => blockTensor (d := d) (D := dimB k) (blocksB k) L)) :
    Σ L : ℕ, PLift (0 < L) ×
      CommonPrimitiveBNTCoverHypotheses (d := d) (p := L)
        (zeroTailA := zeroTailA) (zeroTailB := zeroTailB)
        (DtotA := ∑ j : Fin rA, dimA j) (DtotB := ∑ k : Fin rB, dimB k)
        (fun j => (μA j) ^ L) (fun k => (μB k) ^ L)
        (fun j => blockTensor (d := d) (D := dimA j) (blocksA j) L)
        (fun k => blockTensor (d := d) (D := dimB k) (blocksB k) L) := by
  classical
  let hExists :=
    MPSTensor.exists_common_blockTensor_isInjective_two_of_isNormalCanonicalFormBNT hA hB
  let L : ℕ := Classical.choose hExists
  have hSpec := Classical.choose_spec hExists
  have hL : 0 < L := hSpec.1
  have hInjA : ∀ j : Fin rA,
      IsInjective (blockTensor (d := d) (D := dimA j) (blocksA j) L) := hSpec.2.1
  have hInjB : ∀ k : Fin rB,
      IsInjective (blockTensor (d := d) (D := dimB k) (blocksB k) L) := hSpec.2.2
  exact ⟨L, PLift.up hL,
    ofNormalCanonicalFormBNT_sameMPV_toTensorFromBlocks_zeroTailIdentity_blockPower
      hA hB L hL aLim bLim haCoeff hbCoeff haLim_ne hbLim_ne hSame hZero
      (hNotGpeA L hL) (hNotGpeB L hL) hInjA hInjB⟩

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

/-- A `CommonRepresentativeBNTCoverHypotheses` structure yields the primitive BNT-cover
hypotheses for the representative common-sector families. -/
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
theorem toMPVCommonPhaseCover {d p rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
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

/-! ### Per-block to global proportional gauge

The per-block matchers from `ProportionalDecompositionConclusion` produce, for every
block index `k`, a dimension equality, an invertible matrix `X_k`, and a phase
`ζ_k ≠ 0` with `B (perm k) i = ζ_k • X_k * (cast (A k)) i * X_k⁻¹`.  The records
below package the permutation, per-block dimension equalities, gauge matrices
`X k`, and phases `ζ k` into a single structure, and assemble the per-block
`X_k` into a block-diagonal element of `GL`, the global proportionality matrix
from arXiv:1606.00608, lines 1155–1192 (Corollary II.2, `eq:II:A=XAX`). -/

/-- Per-block gauge-phase data attached to a `ProportionalDecompositionConclusion`.

This is the structural record realizing arXiv:1606.00608, lines 1155–1192
(Corollary II.2, eq. `eq:II:A=XAX`): a permutation matching the block indices,
per-block dimension equalities, and per-block gauge matrices `X k` with phases
`phase k` satisfying
`blocksB (perm k) i = phase k • X k * cast (blocksA k) i * (X k)⁻¹`. -/
structure BlockProportionalGaugePhaseData
    {d rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    (blocksA : (j : Fin rA) → MPSTensor d (dimA j))
    (blocksB : (k : Fin rB) → MPSTensor d (dimB k)) : Type where
  /-- Permutation matching the two block index sets. -/
  perm : Fin rA ≃ Fin rB
  /-- Per-block dimension equality. -/
  hdim : ∀ k : Fin rA, dimA k = dimB (perm k)
  /-- Per-block gauge matrix. -/
  X : (k : Fin rA) → GL (Fin (dimB (perm k))) ℂ
  /-- Per-block phase. -/
  phase : Fin rA → ℂ
  /-- Each per-block phase is nonzero. -/
  phase_ne : ∀ k, phase k ≠ 0
  /-- Per-block conjugation identity with phase. -/
  conj : ∀ k : Fin rA, ∀ i : Fin d,
    blocksB (perm k) i =
      phase k • ((X k : Matrix (Fin (dimB (perm k))) (Fin (dimB (perm k))) ℂ) *
        (cast (congr_arg (MPSTensor d) (hdim k)) (blocksA k)) i *
        (((X k)⁻¹ : GL (Fin (dimB (perm k))) ℂ) :
          Matrix (Fin (dimB (perm k))) (Fin (dimB (perm k))) ℂ))

namespace BlockProportionalGaugePhaseData

variable {d rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
variable {blocksA : (j : Fin rA) → MPSTensor d (dimA j)}
variable {blocksB : (k : Fin rB) → MPSTensor d (dimB k)}

/-- Extract per-block gauge-phase data from a `ProportionalDecompositionConclusion`. -/
noncomputable def ofConclusion
    (h : ProportionalDecompositionConclusion (d := d) blocksA blocksB) :
    BlockProportionalGaugePhaseData blocksA blocksB :=
  let perm := h.choose_spec.choose
  let hperm := h.choose_spec.choose_spec
  let hdim : ∀ k : Fin rA, dimA k = dimB (perm k) :=
    fun k => (hperm k).choose
  let hGP : ∀ k : Fin rA, GaugePhaseEquiv (d := d)
      (cast (congr_arg (MPSTensor d) (hdim k)) (blocksA k)) (blocksB (perm k)) :=
    fun k => (hperm k).choose_spec
  let X : (k : Fin rA) → GL (Fin (dimB (perm k))) ℂ :=
    fun k => (hGP k).choose
  let ζ : Fin rA → ℂ := fun k => (hGP k).choose_spec.choose
  have hζ : ∀ k, ζ k ≠ 0 := fun k => (hGP k).choose_spec.choose_spec.1
  have hX : ∀ k i, blocksB (perm k) i =
      ζ k • ((X k : Matrix (Fin (dimB (perm k))) (Fin (dimB (perm k))) ℂ) *
        (cast (congr_arg (MPSTensor d) (hdim k)) (blocksA k)) i *
        (((X k)⁻¹ : GL (Fin (dimB (perm k))) ℂ) :
          Matrix (Fin (dimB (perm k))) (Fin (dimB (perm k))) ℂ)) :=
    fun k => (hGP k).choose_spec.choose_spec.2
  { perm := perm
    hdim := hdim
    X := X
    phase := ζ
    phase_ne := hζ
    conj := hX }

/-- The reindexed `B`-side block family at the matched dimensions. -/
noncomputable def reindexB (G : BlockProportionalGaugePhaseData blocksA blocksB) :
    (k : Fin rA) → MPSTensor d (dimB (G.perm k)) :=
  fun k => blocksB (G.perm k)

/-- The cast `A`-side block family at the matched dimensions. -/
noncomputable def castA (G : BlockProportionalGaugePhaseData blocksA blocksB) :
    (k : Fin rA) → MPSTensor d (dimB (G.perm k)) :=
  fun k => cast (congr_arg (MPSTensor d) (G.hdim k)) (blocksA k)

/-- The unflattened block-diagonal gauge assembled from the per-block `X k`.

This lives on the dependent sigma-indexed bond space
`(k : Fin rA) × Fin (dimB (G.perm k))`, with diagonal block `X k` over the
matched `B`-side block `G.perm k`.  The flattened/reindexed gauge acting on the
bond dimension of `toTensorFromBlocks` is `G.globalX`. -/
noncomputable def globalGL (G : BlockProportionalGaugePhaseData blocksA blocksB) :
    GL ((k : Fin rA) × Fin (dimB (G.perm k))) ℂ :=
  blockDiagonalGL G.X

/-- The flattened block-diagonal gauge matrix as an element of
`GL (Fin (∑ k, dimB (perm k))) ℂ`, the bond dimension of the assembled tensor.

Defined as the canonical reindexing of `G.globalGL`, so that
`G.globalX = globalGaugeOfBlocks G.X` definitionally. -/
noncomputable def globalX (G : BlockProportionalGaugePhaseData blocksA blocksB) :
    GL (Fin (∑ k : Fin rA, dimB (G.perm k))) ℂ :=
  globalGaugeOfBlocks G.X

/-- Explicit global-gauge witness for the proportional block assembly.

When per-block phases are absorbed into the block weights via
`μA k = μB (perm k) * phase k`, the weighted direct sum of the permuted right
blocks is conjugate to the weighted direct sum of the cast left blocks by
`G.globalX`. -/
theorem toTensorFromBlocks_reindexB_eq_globalX_conj
    (G : BlockProportionalGaugePhaseData blocksA blocksB)
    (μA : Fin rA → ℂ) (μB : Fin rB → ℂ)
    (hμ : ∀ k, μA k = μB (G.perm k) * G.phase k) :
    ∀ i : Fin d,
      toTensorFromBlocks (d := d) (μ := fun k => μB (G.perm k)) G.reindexB i =
        (G.globalX : Matrix (Fin (∑ k : Fin rA, dimB (G.perm k)))
          (Fin (∑ k : Fin rA, dimB (G.perm k))) ℂ) *
          toTensorFromBlocks (d := d) (μ := μA) G.castA i *
          (((G.globalX)⁻¹ : GL (Fin (∑ k : Fin rA, dimB (G.perm k))) ℂ) :
            Matrix (Fin (∑ k : Fin rA, dimB (G.perm k)))
              (Fin (∑ k : Fin rA, dimB (G.perm k))) ℂ) := by
  classical
  have hWeighted :
      ∀ k : Fin rA, ∀ i : Fin d,
        (μB (G.perm k)) • G.reindexB k i =
          (G.X k : Matrix (Fin (dimB (G.perm k))) (Fin (dimB (G.perm k))) ℂ) *
            ((μA k) • G.castA k i) *
            (((G.X k)⁻¹ : GL (Fin (dimB (G.perm k))) ℂ) :
              Matrix (Fin (dimB (G.perm k))) (Fin (dimB (G.perm k))) ℂ) := by
    intro k i
    change (μB (G.perm k)) • blocksB (G.perm k) i =
      (G.X k : Matrix (Fin (dimB (G.perm k))) (Fin (dimB (G.perm k))) ℂ) *
        ((μA k) • G.castA k i) *
        (((G.X k)⁻¹ : GL (Fin (dimB (G.perm k))) ℂ) :
          Matrix (Fin (dimB (G.perm k))) (Fin (dimB (G.perm k))) ℂ)
    rw [G.conj k i, hμ k]
    simp [castA, smul_smul, Matrix.mul_assoc, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  have hFormula :=
    toTensorFromBlocks_eq_globalGaugeOfBlocks_conj
      (μ := fun _ : Fin rA => (1 : ℂ))
      (A := fun k i => μA k • G.castA k i)
      (B := fun k i => μB (G.perm k) • G.reindexB k i)
      G.X hWeighted
  have hLeft :
      toTensorFromBlocks (d := d) (μ := fun _ : Fin rA => (1 : ℂ))
        (fun k i => μA k • G.castA k i) =
        toTensorFromBlocks (d := d) (μ := μA) G.castA := by
    funext i
    simp [toTensorFromBlocks]
  have hRight :
      toTensorFromBlocks (d := d) (μ := fun _ : Fin rA => (1 : ℂ))
        (fun k i => μB (G.perm k) • G.reindexB k i) =
        toTensorFromBlocks (d := d) (μ := fun k => μB (G.perm k)) G.reindexB := by
    funext i
    simp [toTensorFromBlocks]
  intro i
  simpa [globalX, hLeft, hRight] using hFormula i

/-- When per-block phases are absorbed into the block weights via
`μA k = μB (perm k) * phase k`, the per-block conjugation identities assemble into a
gauge equivalence between the weighted block-diagonal tensors built from the cast
left family and the permuted right family. -/
theorem gaugeEquiv_toTensorFromBlocks
    (G : BlockProportionalGaugePhaseData blocksA blocksB)
    (μA : Fin rA → ℂ) (μB : Fin rB → ℂ)
    (hμ : ∀ k, μA k = μB (G.perm k) * G.phase k) :
    GaugeEquiv
      (toTensorFromBlocks (d := d) (μ := μA) G.castA)
      (toTensorFromBlocks (d := d) (μ := fun k => μB (G.perm k)) G.reindexB) := by
  exact ⟨G.globalX, G.toTensorFromBlocks_reindexB_eq_globalX_conj μA μB hμ⟩

end BlockProportionalGaugePhaseData

end MPSTensor

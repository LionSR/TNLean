/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.Assembly.StructuralTheorem
import TNLean.MPS.CanonicalForm.Assembly.SectorComparisonCore

open scoped Matrix BigOperators ComplexOrder MatrixOrder

/-!
# Common primitive proportional data

This file records the span, phase-cover, and BNT-cover hypotheses for common
primitive nonzero-sector families.  These structures express the remaining data
needed to pass from the common-sector structural theorem to the BNT
overlap-rigidity comparison.

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
lemma zeroTail_eq_of_proportionalDecompositionConclusion
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

For non-periodic tensors, the comparison is applied at the BNT-cover level:
the representative/grouping choices are implementation details of the
structural construction, not a separate paper-level hypothesis surface. -/
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
      (d' := blockPhysDim d p) (μ := μA) blocksA hTPA hPrimA hDimA hμA hIrrA
      hAntiA.antitone
  ncfB := by
    have hDimB : ∀ x, 0 < dimB x := fun x => Nat.pos_of_ne_zero (NeZero.ne (dimB x))
    exact isNormalCanonicalForm_of_tp_primitive_irr_sorted
      (d' := blockPhysDim d p) (μ := μB) blocksB hTPB hPrimB hDimB hμB hIrrB
      hAntiB.antitone
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
      (d' := blockPhysDim d p) (μ := μA) blocksA hTPA hPrimA hDimA hμA hIrrA
      hAntiA.antitone
  have hNcfB : IsNormalCanonicalForm (d := blockPhysDim d p) μB blocksB :=
    isNormalCanonicalForm_of_tp_primitive_irr_sorted
      (d' := blockPhysDim d p) (μ := μB) blocksB hTPB hPrimB hDimB hμB hIrrB
      hAntiB.antitone
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

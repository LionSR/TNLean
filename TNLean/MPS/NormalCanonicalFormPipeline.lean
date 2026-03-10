/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.CyclicDecomposition
import TNLean.MPS.Blocking
import TNLean.MPS.CanonicalFormExistence1606
import TNLean.PiAlgebra.CanonicalFormSep

open scoped Matrix BigOperators

/-!
# Normal canonical form existence pipeline

This file records the intended end-to-end assembly

$$A \leadsto \text{irreducible blocks} \leadsto \text{left-canonical / TP gauge}
   \leadsto \text{period blocking + cyclic sector decomposition}
   \leadsto \text{IsNormalCanonicalForm}.$$

The key point is that the periodicity-removal step changes the physical dimension from `d` to
`d^p = blockPhysDim d p`. Consequently, the clean existence statement is formulated **after a
common physical blocking** of the original tensor.

At present, the public theorem is reduced to the initial irreducible decomposition together
with a small stack of private helper lemmas. The remaining gaps are now factored into:

* blockwise Perron--Frobenius / TP gauging,
* single-block cyclic re-decomposition using Wolf Theorem 6.6,
* family-level common-blocking / `SameMPV₂` bookkeeping, and
* final reindexing / merging to obtain strictly decreasing weight moduli.
-/

namespace MPSTensor

variable {d D : ℕ}

/-- Blockwise Perron--Frobenius / TP gauge step for an irreducible block decomposition.

This is the place where zero blocks must be removed or re-indexed carefully (because `SameMPV₂`
remembers the `N = 0` sector), and where the PF rescaling factors from
`exists_tp_data_of_irreducible_pipeline1606` are absorbed into the block weights. -/
private theorem tp_gauge_blockwise
    (A : MPSTensor d D)
    {r0 : ℕ} {dim0 : Fin r0 → ℕ}
    (blocks0 : (k : Fin r0) → MPSTensor d (dim0 k))
    (hIrr0 : ∀ k, IsIrreducibleTensor (blocks0 k))
    (hSame0 :
      SameMPV₂ A
        (toTensorFromBlocks (d := d) (μ := fun _ : Fin r0 => (1 : ℂ)) blocks0)) :
    ∃ r1 : ℕ,
      ∃ dim1 : Fin r1 → ℕ,
      ∃ μ1 : Fin r1 → ℂ,
      ∃ blocks1 : (k : Fin r1) → MPSTensor d (dim1 k),
        SameMPV₂ A
          (toTensorFromBlocks (d := d) (μ := μ1) blocks1) ∧
        (∀ k, IsIrreducibleTensor (blocks1 k)) ∧
        (∀ k, ∑ i : Fin d, (blocks1 k i)ᴴ * blocks1 k i = 1) ∧
        (∀ k, μ1 k ≠ 0) ∧
        (∀ k, 0 < dim1 k) := by
  sorry

/-- Single-block bridge from Wolf Theorem 6.6 to the normal-form pipeline.

Starting from a left-canonical irreducible block, first use
`exists_blockTensor_isPrimitive_pipeline1606` to find a period. Then apply
`exists_cyclic_decomposition_of_irreducible_schwarz` together with
`isIrreducible_restriction_of_cyclic_decomp` and
`isPrimitive_restriction_of_cyclic_decomp` to split the blocked tensor into primitive
irreducible sectors. The output is repackaged as a finite block family with unit weights. -/
private theorem cyclic_redecomp_to_NT
    [NeZero D]
    (A : MPSTensor d D)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hIrr : IsIrreducibleTensor A)
    (hDim : 0 < D) :
    ∃ p : ℕ, 0 < p ∧
      ∃ r : ℕ,
      ∃ dim : Fin r → ℕ,
      ∃ blocks : (k : Fin r) → MPSTensor (blockPhysDim d p) (dim k),
        SameMPV₂
          (blockTensor (d := d) (D := D) A p)
          (toTensorFromBlocks
            (d := blockPhysDim d p)
            (μ := fun _ : Fin r => (1 : ℂ))
            blocks) ∧
        (∀ k, IsIrreducibleTensor (blocks k)) ∧
        (∀ k, ∑ i : Fin (blockPhysDim d p), (blocks k i)ᴴ * blocks k i = 1) ∧
        (∀ k,
          _root_.IsPrimitive
            (transferMap (d := blockPhysDim d p) (D := dim k) (blocks k))) ∧
        (∀ k, 0 < dim k) := by
  sorry

/-- Family-level periodicity removal and cyclic re-decomposition.

This maps `cyclic_redecomp_to_NT` over the TP-gauged irreducible blocks, chooses a common
blocking length, reblocks all sector tensors to the same physical dimension, concatenates the
resulting families, and threads `SameMPV₂` through the entire block-diagonal construction. -/
private theorem common_blocking_primitive
    (A : MPSTensor d D)
    {r1 : ℕ} {dim1 : Fin r1 → ℕ}
    (μ1 : Fin r1 → ℂ)
    (blocks1 : (k : Fin r1) → MPSTensor d (dim1 k))
    (hSame1 :
      SameMPV₂ A
        (toTensorFromBlocks (d := d) (μ := μ1) blocks1))
    (hIrr1 : ∀ k, IsIrreducibleTensor (blocks1 k))
    (hLeft1 : ∀ k, ∑ i : Fin d, (blocks1 k i)ᴴ * blocks1 k i = 1)
    (hμne1 : ∀ k, μ1 k ≠ 0)
    (hDim1 : ∀ k, 0 < dim1 k) :
    ∃ p : ℕ, 0 < p ∧
      ∃ r2 : ℕ,
      ∃ dim2 : Fin r2 → ℕ,
      ∃ μ2 : Fin r2 → ℂ,
      ∃ blocks2 : (k : Fin r2) → MPSTensor (blockPhysDim d p) (dim2 k),
        SameMPV₂
          (blockTensor (d := d) (D := D) A p)
          (toTensorFromBlocks (d := blockPhysDim d p) (μ := μ2) blocks2) ∧
        (∀ k, IsIrreducibleTensor (blocks2 k)) ∧
        (∀ k, ∑ i : Fin (blockPhysDim d p), (blocks2 k i)ᴴ * blocks2 k i = 1) ∧
        (∀ k,
          _root_.IsPrimitive
            (transferMap (d := blockPhysDim d p) (D := dim2 k) (blocks2 k))) ∧
        (∀ k, μ2 k ≠ 0) ∧
        (∀ k, 0 < dim2 k) := by
  sorry

/-- Final strict-weight packaging step.

This is the place where the blocked primitive family is reordered by decreasing modulus and, if
necessary, equal-modulus weights are merged before producing the final `StrictAnti` profile. -/
private theorem weight_assignment
    {p Dblk : ℕ}
    (Ablk : MPSTensor (blockPhysDim d p) Dblk)
    {r2 : ℕ} {dim2 : Fin r2 → ℕ}
    (μ2 : Fin r2 → ℂ)
    (blocks2 : (k : Fin r2) → MPSTensor (blockPhysDim d p) (dim2 k))
    (hSame2 :
      SameMPV₂ Ablk
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μ2) blocks2))
    (hIrr2 : ∀ k, IsIrreducibleTensor (blocks2 k))
    (hLeft2 : ∀ k, ∑ i : Fin (blockPhysDim d p), (blocks2 k i)ᴴ * blocks2 k i = 1)
    (hPrim2 : ∀ k,
      _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := dim2 k) (blocks2 k)))
    (hμne2 : ∀ k, μ2 k ≠ 0)
    (hDim2 : ∀ k, 0 < dim2 k) :
    ∃ r : ℕ,
      ∃ dim : Fin r → ℕ,
      ∃ μ : Fin r → ℂ,
      ∃ blocks : (k : Fin r) → MPSTensor (blockPhysDim d p) (dim k),
        SameMPV₂ Ablk
          (toTensorFromBlocks (d := blockPhysDim d p) (μ := μ) blocks) ∧
        (∀ k, IsIrreducibleTensor (blocks k)) ∧
        (∀ k, ∑ i : Fin (blockPhysDim d p), (blocks k i)ᴴ * blocks k i = 1) ∧
        (∀ k,
          _root_.IsPrimitive
            (transferMap (d := blockPhysDim d p) (D := dim k) (blocks k))) ∧
        StrictAnti (fun k : Fin r => ‖μ k‖) ∧
        (∀ k, μ k ≠ 0) ∧
        (∀ k, 0 < dim k) := by
  sorry

/-- Handoff lemma isolating the remaining gap after the irreducible block decomposition.

Starting from a fixed irreducible block decomposition of `A`, the remaining assembly tasks are now
split into the helper lemmas `tp_gauge_blockwise`, `cyclic_redecomp_to_NT`,
`common_blocking_primitive`, and `weight_assignment`. The present theorem simply composes those
stages into the separated data needed for `IsNormalCanonicalForm`. -/
private theorem exists_blocked_normal_data_of_irreducible_blockDecomp
    (A : MPSTensor d D)
    {r0 : ℕ} {dim0 : Fin r0 → ℕ}
    (blocks0 : (k : Fin r0) → MPSTensor d (dim0 k))
    (hIrr0 : ∀ k, IsIrreducibleTensor (blocks0 k))
    (hSame0 :
      SameMPV₂ A
        (toTensorFromBlocks (d := d) (μ := fun _ : Fin r0 => (1 : ℂ)) blocks0)) :
    ∃ p : ℕ, 0 < p ∧
      ∃ r : ℕ,
      ∃ dim : Fin r → ℕ,
      ∃ μ : Fin r → ℂ,
      ∃ blocks : (k : Fin r) → MPSTensor (blockPhysDim d p) (dim k),
        SameMPV₂
          (blockTensor (d := d) (D := D) A p)
          (toTensorFromBlocks (d := blockPhysDim d p) (μ := μ) blocks) ∧
        (∀ k, IsIrreducibleTensor (blocks k)) ∧
        (∀ k, ∑ i : Fin (blockPhysDim d p), (blocks k i)ᴴ * blocks k i = 1) ∧
        (∀ k,
          _root_.IsPrimitive
            (transferMap (d := blockPhysDim d p) (D := dim k) (blocks k))) ∧
        StrictAnti (fun k : Fin r => ‖μ k‖) ∧
        (∀ k, μ k ≠ 0) ∧
        (∀ k, 0 < dim k) := by
  obtain ⟨r1, dim1, μ1, blocks1, hSame1, hIrr1, hLeft1, hμne1, hDim1⟩ :=
    tp_gauge_blockwise (A := A) (r0 := r0) (dim0 := dim0) blocks0 hIrr0 hSame0
  obtain ⟨p, hp, r2, dim2, μ2, blocks2, hSame2, hIrr2, hLeft2, hPrim2, hμne2, hDim2⟩ :=
    common_blocking_primitive
      (A := A) (r1 := r1) (dim1 := dim1) (μ1 := μ1) blocks1
      hSame1 hIrr1 hLeft1 hμne1 hDim1
  obtain ⟨r, dim, μ, blocks, hSame, hIrr, hLeft, hPrim, hμanti, hμne, hDim⟩ :=
    weight_assignment
      (d := d)
      (p := p)
      (Ablk := blockTensor (d := d) (D := D) A p)
      (r2 := r2) (dim2 := dim2) (μ2 := μ2) blocks2
      hSame2 hIrr2 hLeft2 hPrim2 hμne2 hDim2
  exact ⟨p, hp, r, dim, μ, blocks, hSame, hIrr, hLeft, hPrim, hμanti, hμne, hDim⟩

/-- Package the separated blocked data into the bundled `IsNormalCanonicalForm` predicate. -/
private theorem exists_normalCanonicalForm_of_irreducible_blockDecomp
    (A : MPSTensor d D)
    {r0 : ℕ} {dim0 : Fin r0 → ℕ}
    (blocks0 : (k : Fin r0) → MPSTensor d (dim0 k))
    (hIrr0 : ∀ k, IsIrreducibleTensor (blocks0 k))
    (hSame0 :
      SameMPV₂ A
        (toTensorFromBlocks (d := d) (μ := fun _ : Fin r0 => (1 : ℂ)) blocks0)) :
    ∃ p : ℕ, 0 < p ∧
      ∃ r : ℕ,
      ∃ dim : Fin r → ℕ,
      ∃ μ : Fin r → ℂ,
      ∃ blocks : (k : Fin r) → MPSTensor (blockPhysDim d p) (dim k),
        SameMPV₂
          (blockTensor (d := d) (D := D) A p)
          (toTensorFromBlocks (d := blockPhysDim d p) (μ := μ) blocks) ∧
        IsNormalCanonicalForm (d := blockPhysDim d p) μ blocks := by
  obtain ⟨p, hp, r, dim, μ, blocks, hSame, hIrr, hLeft, hPrim, hμanti, hμne, hDim⟩ :=
    exists_blocked_normal_data_of_irreducible_blockDecomp
      (A := A) (r0 := r0) (dim0 := dim0) blocks0 hIrr0 hSame0
  refine ⟨p, hp, r, dim, μ, blocks, hSame, ?_⟩
  let hμ : HasStrictOrderedNonzeroWeights μ := {
    mu_strict_anti := hμanti
    mu_ne_zero := hμne
  }
  exact
    IsNormalCanonicalForm.ofSeparatedData
      (d := blockPhysDim d p)
      (A := blocks)
      (μ := μ)
      (HasIrreducibleBlocks.ofForall hIrr)
      (IsLeftCanonicalBlockFamily.ofForall hLeft)
      (HasPrimitiveBlocks.ofForall hPrim)
      hμ
      hDim

/-- **Existence of a normal canonical form after a common physical blocking.**

For an arbitrary tensor `A`, there exist:

* a common blocking length `p > 0`,
* a finite family of bond dimensions `dim k`,
* nonzero block weights `μ k`, strictly decreasing in modulus,
* blocked tensors `blocks k`,

such that the physically blocked tensor `blockTensor A p` is `SameMPV₂`-equivalent to the
block-diagonal tensor `toTensorFromBlocks μ blocks`, and the latter satisfies
`IsNormalCanonicalForm`.

This is the correct shape for the pipeline because different irreducible blocks may require
*different* periodicity-removal lengths; one therefore takes a common multiple and compares after
blocking the original tensor as well.

Proof outline:

1. decompose `A` into irreducible blocks using
   `exists_irreducible_blockDecomp_pipeline1606`;
2. put each nontrivial irreducible block into the left-canonical / TP gauge using
   `exists_tp_data_of_irreducible_pipeline1606`, absorbing the PF scaling into the block weight;
3. choose a common blocking length from the blockwise witnesses produced by
   `exists_blockTensor_isPrimitive_pipeline1606`;
4. block every surviving block by that common length, reorder by decreasing `‖μ k‖`, and package
   the hypotheses into `IsNormalCanonicalForm`.

The remaining proof work is largely dependent bookkeeping rather than new mathematics. -/
theorem exists_normalCanonicalForm (A : MPSTensor d D) :
    ∃ p : ℕ, 0 < p ∧
      ∃ r : ℕ,
      ∃ dim : Fin r → ℕ,
      ∃ μ : Fin r → ℂ,
      ∃ blocks : (k : Fin r) → MPSTensor (blockPhysDim d p) (dim k),
        SameMPV₂
          (blockTensor (d := d) (D := D) A p)
          (toTensorFromBlocks (d := blockPhysDim d p) (μ := μ) blocks) ∧
        IsNormalCanonicalForm (d := blockPhysDim d p) μ blocks := by
  obtain ⟨r, dim, blocks, hIrr, hSame⟩ :=
    exists_irreducible_blockDecomp_pipeline1606 (d := d) (D := D) A
  exact
    exists_normalCanonicalForm_of_irreducible_blockDecomp
      (A := A) (r0 := r) (dim0 := dim) blocks hIrr hSame

end MPSTensor

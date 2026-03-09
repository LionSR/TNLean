/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Blocking
import TNLean.MPS.CanonicalFormExistence1606
import TNLean.PiAlgebra.CanonicalFormSep

open scoped Matrix BigOperators

/-!
# Normal canonical form existence pipeline

This file records the intended end-to-end assembly

$$A \leadsto \text{irreducible blocks} \leadsto \text{left-canonical / TP gauge}
   \leadsto \text{period blocking} \leadsto \text{IsNormalCanonicalForm}.$$

The key point is that the periodicity-removal step changes the physical dimension from `d` to
`d^p = blockPhysDim d p`. Consequently, the clean existence statement is formulated **after a
common physical blocking** of the original tensor.

At present, the main theorem is reduced to step (1) of the pipeline together with a packaging
lemma, while the remaining nontrivial bookkeeping is isolated in a single private `sorry`
(blockwise PF gauges, common blocking length, zero-block disposal, and reordering by decreasing
weight modulus).
-/

namespace MPSTensor

variable {d D : ℕ}

/-- Handoff lemma isolating the remaining bookkeeping after the irreducible block decomposition.

Starting from a fixed irreducible block decomposition of `A`, the remaining assembly tasks are:

1. apply `exists_tp_data_of_irreducible_pipeline1606` to each nonzero block and absorb the
   Perron--Frobenius rescaling into the block weights;
2. apply `exists_blockTensor_isPrimitive_pipeline1606` blockwise, choose a common blocking length,
   and reblock all surviving blocks to the same physical dimension;
3. reorder / merge the resulting weighted blocks so that the final weights are strictly decreasing
   in modulus;
4. thread the resulting `SameMPV₂` equivalence through blocking and block-diagonal assembly.

The theorem below isolates exactly that bookkeeping package. It is the only remaining gap in the
end-to-end pipeline. -/
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
  /-
  TODO:
  * discard zero irreducible blocks (the TP-gauge wrapper assumes a nonzero Kraus operator);
  * apply `exists_tp_data_of_irreducible_pipeline1606` to each surviving block and record the
    induced nonzero complex weights;
  * apply `exists_blockTensor_isPrimitive_pipeline1606` blockwise, choose a common blocking length,
    and convert the blockwise outputs to a single family over `Fin r`;
  * thread `SameMPV₂` through gauge equivalence, blocking, and `toTensorFromBlocks`;
  * reorder / merge blocks so that the final weights satisfy `StrictAnti`.
  -/
  sorry

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

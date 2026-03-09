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

At present, the theorem below is a scaffold: the statement is chosen to match the already formalized
interfaces, while the proof still contains a `sorry` for the nontrivial bookkeeping steps
(blockwise PF gauges, common blocking length, zero-block disposal, and reordering by decreasing
weight modulus).
-/

namespace MPSTensor

variable {d D : ℕ}

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
  /-
  Intended assembly:

  * irreducible decomposition of `A`;
  * blockwise PF / left-canonical gauge, producing weights from the PF radii;
  * common multiple of the block periods;
  * blocking, reordering, and packaging into `IsNormalCanonicalForm`.
  -/
  sorry

end MPSTensor

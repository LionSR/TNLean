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

/-- Handoff lemma isolating the remaining gap after the irreducible block decomposition.

Starting from a fixed irreducible block decomposition of `A`, the remaining assembly tasks are:

1. apply `exists_tp_data_of_irreducible_pipeline1606` to each nonzero block and absorb the
   Perron--Frobenius rescaling into the block weights;
2. apply `exists_blockTensor_isPrimitive_pipeline1606` blockwise, choose a common blocking length,
   and reblock all surviving blocks to the same physical dimension;
3. **re-decompose** each blocked tensor into primitive irreducible sectors (blocking a periodic
   irreducible tensor by its period gives `IsPrimitive (transferMap ...)` but NOT necessarily
   `IsIrreducibleTensor`, since the blocked transfer map `E^p` may be reducible with `p`
   invariant subspaces);
4. reorder / merge the resulting weighted blocks so that the final weights are strictly decreasing
   in modulus;
5. thread the resulting `SameMPV₂` equivalence through blocking and block-diagonal assembly.

**Known issues with the current statement** (identified 2026-03-10):

* Step (3) is a genuine mathematical gap, not just bookkeeping. After blocking an irreducible
  tensor with period `p`, the blocked tensor's transfer map `E^p` is primitive
  (`peripheral eigenvalues = {1}`) but may be **reducible** (with `p` invariant subspaces from
  the cyclic decomposition). The correct fix is an additional irreducible re-decomposition step
  after blocking.
* `StrictAnti (fun k => ‖μ k‖)` requires merging blocks with equal PF radii, which is a
  nontrivial re-indexing step.
* Zero-dimensional or all-zero blocks need special handling since
  `exists_tp_data_of_irreducible_pipeline1606` requires `∃ i, A i ≠ 0`.

Despite these issues, the **downstream FT chain from `IsNormalCanonicalForm` to the final theorem
is completely sorry-free**. This sorry only affects the "arbitrary tensor → normal canonical form"
direction. -/
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
  Remaining sub-tasks (see docstring for known issues):
  1. Handle zero blocks (discard or re-index, with care for N=0 MPV compatibility).
  2. Apply TP gauge blockwise (`exists_tp_data_of_irreducible_pipeline1606`).
  3. Common blocking period (`exists_blockTensor_isPrimitive_pipeline1606`).
  4. **Re-decompose** blocked tensors into primitive irreducible sectors
     (this is the main mathematical gap — blocking a period-p irreducible tensor gives a
     reducible transfer map E^p with p invariant subspaces).
  5. Thread `SameMPV₂` through gauge equivalence, blocking, and `toTensorFromBlocks`.
  6. Reorder/merge blocks for `StrictAnti` weight ordering.
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

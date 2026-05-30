/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.NormalReduction
import TNLean.MPS.CanonicalForm.CyclicSectors
import TNLean.MPS.CanonicalForm.CommonPeriodCyclicSectors
import TNLean.MPS.Core.BlockingInfrastructure
import TNLean.MPS.Core.BlockingTransfer
import TNLean.MPS.Overlap.PeripheralToTransferMapGap
import TNLean.MPS.SharedInfra.KrausAdjointSetup
import TNLean.Channel.Peripheral.CyclicDecomposition
import TNLean.Channel.Peripheral.GroupStructure
import TNLean.Wielandt.SpanGrowth.VectorToMatrixSpan
import TNLean.Wielandt.SpanGrowth.CumulativeSpan
import TNLean.Wielandt.RectangularSpan.Basic
import TNLean.Wielandt.Primitivity.ToNormal
import TNLean.Wielandt.Primitivity.StronglyIrreducibleToFullRank

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Filter

/-!
# TP-primitive reduction after blocking

This file begins the canonical-form reduction for arbitrary MPS
families. It combines the zero-block separation, TP gauge, and
common blocking steps into a blocked decomposition whose nontrivial blocks are
left-canonical and have primitive transfer maps.

The "zero tail" in the produced decomposition is the total bond dimension of
the separated all-zero leftover blocks.  It is the dimension gap allowed by
`∑ k, D_k ≤ D`, where the remaining summands are zero blocks.

## Main statements

* `exists_tp_primitive_blockDecomp_after_blocking` — arbitrary tensors admit a
  positive-length blocked decomposition into TP-primitive blocks, together with
  the separate zero-block bond-dimension count.

## References

* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608, Section 2.3 + Appendix A]
* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:2011.12127, Section IV]

## External inputs

This file is the main integration point for the Quantum Wielandt machinery in the
canonical-form reduction.  It imports four Wielandt modules:

1. **`Wielandt.SpanGrowth.VectorToMatrixSpan`** — the vector-to-matrix spanning step
   (arXiv:0909.5347, Lemma 2(a)/Wolf Chapter 6): if a vector-valued linear image of the
   Kraus word products spans the full vector space, then the matrix-valued word products
   span the full matrix algebra.

2. **`Wielandt.SpanGrowth.CumulativeSpan`** — the cumulative span growth machinery
   (arXiv:0909.5347, Lemma 1): the cumulative span `S_n(A)` grows strictly until it
   reaches the full matrix algebra, with an explicit bound on the stopping time.

3. **`Wielandt.RectangularSpan.Basic`** — the rectangular span theory for Wielandt
   Lemma 2(b): `wielandt_lemma2b_conditional` reduces the full-rank conclusion to
   finding a rank-one element in the word span.

4. **`Wielandt.Primitivity.StronglyIrreducibleToFullRank`** — the hardest direction
   of the primitivity equivalence (Proposition 3(a)→(c) of arXiv:0909.5347): strong
   irreducibility of the transfer map implies `krausRank A = D`.

5. **`Wielandt.Primitivity.ToNormal`** — the primitivity-to-normality implication:
   when the peripheral spectrum condition is satisfied, the transfer map becomes normal
   (commutes with its adjoint), which unlocks the full Wielandt chain.

Together, these inputs supply the fact that a TP-primitive block (after the
Perron-Frobenius gauge and periodicity blocking) is injective — its Kraus operators
span the full matrix algebra at length 1, and therefore block-injective at every
positive length.  This is the mathematical content that justifies the
"primitive ⇒ injective" implication used in the blocked canonical-form decomposition.

## Tags

matrix product states, canonical form, blocking, primitive transfer maps
-/

namespace MPSTensor

variable {d D : ℕ}

/-!
## The main reduction theorem

We compose the individual reduction steps into a single theorem that takes
an arbitrary `A : MPSTensor d D` and produces blocked TP-primitive data.
-/

/-- **Main reduction: arbitrary MPS tensor → blocked TP-primitive decomposition.**

For any `A : MPSTensor d D`, there exists a blocking period `p > 0` and
a decomposition:

* a **trivial block** of dimension `zeroTailDim` (accumulating all-zero irreducible
  blocks from the original decomposition);
* a family of **weighted blocked blocks** `blocks k` indexed by `Fin r`, each with:
  - left-canonical (TP) normalization `∑ᵢ (blocks k i)ᴴ * (blocks k i) = I`;
  - primitive transfer map `_root_.IsPrimitive (transferMap (blocks k))`;
  - positive bond dimension;
  - nonzero weight `μ k`.

The MPV relationship holds at every positive blocked length:
```
  mpv (blockTensor A p) σ = mpv (toTensorFromBlocks μ blocks) σ
```

The zero block appears only through the length-zero bond-dimension identity
`zeroTailDim + ∑ dim = D`. This separates the source's positive-length
comparison from the empty-word dimension count, as described in
`docs/paper-gaps/cpsv16_zero_tail_length_zero_decomposition.tex`.

**Note on the original blocks**: The pre-blocking blocks (from step 2) ARE
`IsIrreducibleTensor`, but blocking does not in general preserve tensor
irreducibility. See the module documentation for the gap analysis. -/
theorem exists_tp_primitive_blockDecomp_after_blocking (A : MPSTensor d D) :
    ∃ (zeroTailDim : ℕ) (p : ℕ) (_ : 0 < p)
      (r : ℕ) (dim : Fin r → ℕ) (μ : Fin r → ℂ)
      (blocks : (k : Fin r) → MPSTensor (blockPhysDim d p) (dim k)),
      -- (a) Blocks are left-canonical (TP)
      (∀ k, ∑ i : Fin (blockPhysDim d p),
        (blocks k i)ᴴ * blocks k i = 1) ∧
      -- (b) Blocks have primitive transfer maps
      (∀ k, _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := dim k) (blocks k))) ∧
      -- (c) Positive bond dimensions
      (∀ k, 0 < dim k) ∧
      -- (d) Nonzero weights
      (∀ k, μ k ≠ 0) ∧
      -- (e) Positive-length MPV relationship
      SameMPV₂Pos
        (blockTensor (d := d) (D := D) A p)
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μ) blocks) ∧
      -- (f) Length-zero bond-dimension count
      zeroTailDim + ∑ k : Fin r, dim k = D := by
  classical
  -- Step A: Get TP-gauged irreducible blocks from an arbitrary tensor.
  obtain ⟨zeroTailDim, r₀, dim₀, μ₀, blocks₀,
      hIrr₀, hTP₀, hμNe₀, hDim₀, hPos₀, hDimId₀⟩ :=
    exists_tp_gauge_from_arbitrary_with_zeroTail (d := d) (D := D) A
  -- Step B: Find a common blocking period making all transfer maps primitive.
  obtain ⟨P, hP, hPrim⟩ :=
    exists_common_blocking_all_primitive_of_TP_irr blocks₀ hTP₀ hIrr₀ hDim₀
  -- Step C: Construct the blocked data.
  set blocks₁ : (k : Fin r₀) → MPSTensor (blockPhysDim d P) (dim₀ k) :=
    fun k => blockTensor (d := d) (D := dim₀ k) (blocks₀ k) P with blocks₁_def
  set μ₁ : Fin r₀ → ℂ := fun k => (μ₀ k) ^ P with μ₁_def
  -- Step D: Verify all properties.
  refine ⟨zeroTailDim, P, hP, r₀, dim₀, μ₁, blocks₁, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- (a) TP under blocking.
  · intro k
    exact leftCanonical_blockTensor (d := d) (D := dim₀ k) (A := blocks₀ k) (L := P) (hTP₀ k)
  -- (b) Primitive transfer maps.
  · exact hPrim
  -- (c) Positive bond dimensions (unchanged by blocking).
  · exact hDim₀
  -- (d) Nonzero weights: `(μ₀ k)^P` remains nonzero since `μ₀ k ≠ 0`.
  · exact blockWeights_ne_zero μ₀ hμNe₀ P
  -- (e) Positive-length MPV relationship.
  · simpa [μ₁_def, blocks₁_def] using
      sameMPV₂Pos_blockTensor_toTensorFromBlocks
        (d := d) (D := D) (r := r₀) (dim := dim₀)
        A μ₀ blocks₀ hPos₀ P hP
  -- (f) Length-zero bond-dimension count.
  · exact hDimId₀.symm

end MPSTensor

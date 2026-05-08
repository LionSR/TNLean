/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.NormalReduction
import TNLean.MPS.CanonicalForm.CyclicSectors
import TNLean.MPS.CanonicalForm.CommonPeriodCyclicSectors
import TNLean.MPS.CanonicalForm.SectorComparison.ZeroTailTransport
import TNLean.MPS.Core.BlockingInfrastructure
import TNLean.MPS.Core.BlockingTransfer
import TNLean.MPS.FundamentalTheorem.EqualProportional
import TNLean.MPS.Overlap.PeripheralToSpectralGap
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

It also includes two immediate consequences when extra hypotheses are already
available: the sorted normal-canonical-form criterion for blocked primitive
families and the trivial-blocking shortcut for tensors that already come with a
primitive block decomposition.

## Main statements

* `exists_tp_primitive_blockDecomp_after_blocking` — arbitrary tensors admit a
  blocked decomposition into a zero tail and TP-primitive blocks.
* `isNormalCanonicalForm_of_tp_primitive_irr_sorted` — a blocked TP-primitive
  family with irreducible blocks and non-increasing weights is already in
  normal canonical form.
* `exists_normalCanonicalForm_of_primitive_input` — primitive block data with
  distinct weight norms yields a normal canonical form without nontrivial
  blocking.

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
   Lemma 2(b): provides the conditional assembly `wielandt_lemma2b_conditional` that
   reduces the full-rank conclusion to finding a rank-one element in the word span.

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

The MPV relationship holds:
```
  mpv (blockTensor A p) σ = mpv (zeroMPSTensor (blockPhysDim d p) zeroTailDim) σ
    + mpv (toTensorFromBlocks μ blocks) σ
```

In particular, for system sizes `N > 0`, the trivial block vanishes and
`blockTensor A p` has the same MPVs as `toTensorFromBlocks μ blocks`.

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
      -- (e) MPV relationship
      (∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d p)),
        mpv (blockTensor (d := d) (D := D) A p) σ =
          mpv (zeroMPSTensor (blockPhysDim d p) zeroTailDim) σ +
            mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μ) blocks) σ) := by
  classical
  -- Step A: Get TP-gauged irreducible blocks from an arbitrary tensor.
  obtain ⟨zeroTailDim, r₀, dim₀, μ₀, blocks₀, hIrr₀, hTP₀, hμNe₀, hDim₀, hMPV₀⟩ :=
    exists_tp_gauge_from_arbitrary_with_zeroTail (d := d) (D := D) A
  -- Step B: Find a common blocking period making all transfer maps primitive.
  obtain ⟨P, hP, hPrim⟩ :=
    exists_common_blocking_all_primitive_of_TP_irr blocks₀ hTP₀ hIrr₀ hDim₀
  -- Step C: Construct the blocked data.
  set blocks₁ : (k : Fin r₀) → MPSTensor (blockPhysDim d P) (dim₀ k) :=
    fun k => blockTensor (d := d) (D := dim₀ k) (blocks₀ k) P with blocks₁_def
  set μ₁ : Fin r₀ → ℂ := fun k => (μ₀ k) ^ P with μ₁_def
  -- Step D: Verify all properties.
  refine ⟨zeroTailDim, P, hP, r₀, dim₀, μ₁, blocks₁, ?_, ?_, ?_, ?_, ?_⟩
  -- (a) TP under blocking.
  · intro k
    exact leftCanonical_blockTensor (d := d) (D := dim₀ k) (A := blocks₀ k) (L := P) (hTP₀ k)
  -- (b) Primitive transfer maps.
  · exact hPrim
  -- (c) Positive bond dimensions (unchanged by blocking).
  · exact hDim₀
  -- (d) Nonzero weights: `(μ₀ k)^P` remains nonzero since `μ₀ k ≠ 0`.
  · exact blockWeights_ne_zero μ₀ hμNe₀ P
  -- (e) MPV relationship.
  · simpa [μ₁_def, blocks₁_def] using
      zeroTail_toTensorFromBlocks_blockPower
        (d := d) (D := D) (r := r₀) (z := zeroTailDim) (p := P) (dim := dim₀)
        A μ₀ blocks₀ hP hMPV₀

/-!
## Conditional normal canonical form

If the blocked weights are ordered by non-increasing norm, and the blocked
blocks are irreducible, then the data can be shown to satisfy
`IsNormalCanonicalForm`.  Equal weight moduli are allowed; requiring pairwise
distinct norms is only a restricted separated-representative branch.

This is a conditional theorem: the extra hypotheses are genuine conditions
that the reduction does not produce automatically (see gap documentation above).
-/

/-- **Conditional normal canonical form after blocking.**

If the blocked data additionally satisfy tensor irreducibility for each block,
and the weight moduli are already sorted in non-increasing order, then the data
forms an `IsNormalCanonicalForm` directly.  Equal moduli are allowed here, as in
the canonical form of arXiv:1606.00608; strict separation belongs only to the
restricted strict-representative branch.

For the unsorted case, use `exists_normalCanonicalForm_of_primitive_blockDecomp`
which handles both sorting and blocking internally. -/
theorem isNormalCanonicalForm_of_tp_primitive_irr_sorted
    {d' : ℕ}
    {r : ℕ} {dim : Fin r → ℕ}
    {μ : Fin r → ℂ}
    (blocks : (k : Fin r) → MPSTensor d' (dim k))
    (hTP : ∀ k, ∑ i : Fin d', (blocks k i)ᴴ * blocks k i = 1)
    (hPrim : ∀ k, _root_.IsPrimitive (transferMap (d := d') (D := dim k) (blocks k)))
    (hDim : ∀ k, 0 < dim k)
    (hμne : ∀ k, μ k ≠ 0)
    (hIrr : ∀ k, IsIrreducibleTensor (blocks k))
    (hAnti : Antitone (fun k : Fin r => ‖μ k‖)) :
    IsNormalCanonicalForm (d := d') μ blocks :=
  IsNormalCanonicalForm.ofSeparatedData
    (HasIrreducibleBlocks.ofForall hIrr)
    (IsLeftCanonicalBlockFamily.ofForall hTP)
    (HasPrimitiveBlocks.ofForall hPrim)
    { mu_antitone := hAnti
      mu_ne_zero := hμne }
    hDim

/-!
## Reduction shortcut for pre-primitive blocks

When the tensor already has primitive blocks with distinct weight norms
(e.g., from an external construction or a tensor that is already aperiodic),
the blocking step is trivial (p = 1) and the full `IsNormalCanonicalForm`
follows directly via `exists_normalCanonicalForm_of_primitive_blockDecomp`.
-/

/-- **Reduction shortcut for pre-primitive blocks.**

If an arbitrary tensor `A` already admits a primitive block decomposition with
pairwise distinct weight norms, then the normal canonical form exists after
trivial blocking (p = 1). -/
theorem exists_normalCanonicalForm_of_primitive_input
    (A : MPSTensor d D)
    {r₁ : ℕ} {dim₁ : Fin r₁ → ℕ}
    (μ₁ : Fin r₁ → ℂ)
    (blocks₁ : (k : Fin r₁) → MPSTensor d (dim₁ k))
    (hSame₁ : SameMPV₂ A (toTensorFromBlocks (d := d) (μ := μ₁) blocks₁))
    (hIrr₁ : ∀ k, IsIrreducibleTensor (blocks₁ k))
    (hTP₁ : ∀ k, ∑ i : Fin d, (blocks₁ k i)ᴴ * blocks₁ k i = 1)
    (hPrim₁ : ∀ k,
      _root_.IsPrimitive (transferMap (d := d) (D := dim₁ k) (blocks₁ k)))
    (hDistinct : ∀ j k, j ≠ k → ‖μ₁ j‖ ≠ ‖μ₁ k‖)
    (hμne₁ : ∀ k, μ₁ k ≠ 0)
    (hDim₁ : ∀ k, 0 < dim₁ k) :
    ∃ p : ℕ, 0 < p ∧
      ∃ r : ℕ,
      ∃ dim : Fin r → ℕ,
      ∃ μ : Fin r → ℂ,
      ∃ blocks : (k : Fin r) → MPSTensor (blockPhysDim d p) (dim k),
        SameMPV₂
          (blockTensor (d := d) (D := D) A p)
          (toTensorFromBlocks (d := blockPhysDim d p) (μ := μ) blocks) ∧
        IsNormalCanonicalForm (d := blockPhysDim d p) μ blocks :=
  exists_normalCanonicalForm_of_primitive_blockDecomp
    A μ₁ blocks₁ hSame₁ hIrr₁ hTP₁ hPrim₁ hDistinct hμne₁ hDim₁

end MPSTensor

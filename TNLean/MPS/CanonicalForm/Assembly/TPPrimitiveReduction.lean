/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.NormalReduction
import TNLean.MPS.CanonicalForm.CyclicSectors
import TNLean.MPS.CanonicalForm.CyclicSectorAssembly
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

This file begins the end-to-end canonical-form reduction for arbitrary MPS
families. It packages the output of the zero-block separation, TP gauge, and
common blocking steps into a blocked decomposition whose nontrivial blocks are
left-canonical and have primitive transfer maps.

It also records two immediate consequences when extra hypotheses are already
available: the sorted normal-canonical-form criterion for blocked primitive
families and the trivial-blocking shortcut for inputs that already come with a
primitive block decomposition.

## Main statements

* `exists_tp_primitive_blockDecomp_after_blocking` — arbitrary tensors admit a
  blocked decomposition into a zero tail and TP-primitive blocks.
* `isNormalCanonicalForm_of_tp_primitive_irr_sorted` — a blocked TP-primitive
  family with irreducible blocks and strictly separated weights is already in
  normal canonical form.
* `exists_normalCanonicalForm_of_primitive_input` — primitive input data with
  distinct weight norms yields a normal canonical form without nontrivial
  blocking.

## References

* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608, §2.3 + Appendix A]
* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:2011.12127, §IV]

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
  -- Step A: Get TP-gauged irreducible blocks from arbitrary input.
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
  -- (d) Nonzero weights: (μ₀ k)^P ≠ 0 since μ₀ k ≠ 0.
  · intro k
    exact pow_ne_zero P (hμNe₀ k)
  -- (e) MPV relationship.
  · intro N σ
    -- Build the flattened configuration σflat : Fin (N * P) → Fin d.
    set flat : List (Fin d) := flattenBlockedWord d P (List.ofFn σ) with flat_def
    have hlen : flat.length = N * P := by
      simpa [flat_def] using (length_flattenBlockedWord (d := d) (L := P) (List.ofFn σ))
    set σflat : Fin (N * P) → Fin d :=
      fun i => flat.get (Fin.cast hlen.symm i) with σflat_def
    have hofFn : List.ofFn σflat = flat := by
      rw [σflat_def]
      conv_rhs => rw [← List.ofFn_get flat]
      have hcongr :=
        (List.ofFn_congr (m := N * P) (n := flat.length) hlen.symm
          (fun i : Fin (N * P) => flat.get (Fin.cast hlen.symm i)))
      simpa [Function.comp, Fin.cast_cast] using hcongr
    -- Key: for ANY tensor T, mpv (blockTensor T P) σ = mpv T σflat.
    have hblock (D' : ℕ) (T : MPSTensor d D') :
        mpv (blockTensor (d := d) (D := D') T P) σ = mpv T σflat := by
      simp [mpv, coeff, hofFn, flat_def, evalWord_blockTensor]
    -- LHS: mpv (blockTensor A P) σ = mpv A σflat.
    rw [hblock D A]
    -- Pre-blocking MPV identity: mpv A σflat = zero-tail + live-blocks.
    rw [hMPV₀ (N * P) σflat]
    -- Trivial block: both sides equal `if N = 0 then zeroTailDim else 0`.
    have hNP_iff : N * P = 0 ↔ N = 0 := by
      rw [Nat.mul_eq_zero]
      exact ⟨fun h => h.resolve_right hP.ne', fun h => Or.inl h⟩
    have hZero :
        mpv (zeroMPSTensor d zeroTailDim) σflat =
          mpv (zeroMPSTensor (blockPhysDim d P) zeroTailDim) σ := by
      rw [mpv_zeroMPSTensor, mpv_zeroMPSTensor]
      simp [hNP_iff]
    rw [hZero]
    -- Live blocks: expand both sides via toTensorFromBlocks.
    congr 1
    rw [mpv_toTensorFromBlocks_eq_sum (μ := μ₀) (A := blocks₀) (σ := σflat)]
    rw [mpv_toTensorFromBlocks_eq_sum (μ := μ₁) (A := blocks₁) (σ := σ)]
    refine Finset.sum_congr rfl fun k _ => ?_
    -- Weights: (μ₀ k)^(N*P) = ((μ₀ k)^P)^N = (μ₁ k)^N.
    have hpow : (μ₀ k) ^ (N * P) = (μ₁ k) ^ N := by
      simp [μ₁_def, Nat.mul_comm, pow_mul]
    rw [hpow]
    -- Block MPV: mpv (blocks₀ k) σflat = mpv (blockTensor (blocks₀ k) P) σ.
    congr 1
    exact (hblock (dim₀ k) (blocks₀ k)).symm

/-!
## Conditional normal canonical form

If the blocked weights happen to have pairwise distinct norms, and the blocked
blocks are irreducible, then the data can be packaged as `IsNormalCanonicalForm`
after sorting by weight norm.

This is a conditional theorem: the two extra hypotheses are genuine conditions
that the reduction does not produce automatically (see gap documentation above).
-/

/-- **Conditional normal canonical form after blocking.**

If the blocked output additionally satisfies tensor irreducibility for each block,
pairwise distinct weight norms, and strict weight ordering (already sorted), then
the data forms an `IsNormalCanonicalForm` directly.

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
    (hAnti : StrictAnti (fun k : Fin r => ‖μ k‖)) :
    IsNormalCanonicalForm (d := d') μ blocks :=
  IsNormalCanonicalForm.ofStrictSeparatedData
    (HasIrreducibleBlocks.ofForall hIrr)
    (IsLeftCanonicalBlockFamily.ofForall hTP)
    (HasPrimitiveBlocks.ofForall hPrim)
    { mu_strict_anti := hAnti
      mu_ne_zero := hμne }
    hDim

/-!
## Reduction shortcut for pre-primitive blocks

When the input already has primitive blocks with distinct weight norms
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

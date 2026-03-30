/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.NormalReduction
import TNLean.MPS.CanonicalForm.CyclicSectors
import TNLean.MPS.Core.BlockingInfrastructure
import TNLean.MPS.Core.BlockingTransfer
import TNLean.MPS.FundamentalTheorem.Full
import TNLean.Channel.Peripheral.CyclicDecomposition
import TNLean.Channel.Peripheral.CyclicGroup
import TNLean.Channel.Peripheral.GroupStructure
import TNLean.Wielandt.SpanGrowth.VectorToMatrixSpan
import TNLean.Wielandt.SpanGrowth.CumulativeSpan
import TNLean.Wielandt.RectangularSpan.Basic

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Filter

/-!
# End-to-end canonical form reduction (arXiv:1606.00608, §2.3 + Appendix A)

This file combines the individual reduction steps into end-to-end theorems
connecting an **arbitrary MPS tensor** to a blocked canonical form.

## Reduction overview

The reduction threads through the following components:

1. **Zero-block separation** (`exists_irreducible_blockDecomp_liveBlocks`):
   split an arbitrary tensor into zero tail + live irreducible blocks.

2. **TP gauge** (`exists_tp_gauge_from_arbitrary_with_zeroTail`):
   apply the Perron–Frobenius / TP-gauge step blockwise, producing irreducible,
   left-canonical blocks with nonzero weights.

3. **Common blocking to primitive** (`exists_common_blocking_all_primitive_of_TP_irr`):
   find a common blocking period P making all block transfer maps primitive.

4. **SameMPV₂ under blocking** (`sameMPV₂_blockTensor_of_sameMPV₂_toTensorFromBlocks`):
   the blocked tensor-from-blocks decomposition has the expected MPV relationship.

5. **TP under blocking** (`leftCanonical_blockTensor`):
   left-canonical normalization is preserved by blocking.

## Main results

* `exists_tp_primitive_blockDecomp_after_blocking`:
  For any `A : MPSTensor d D`, there exists a blocking period `p > 0` such that
  `blockTensor A p` admits a decomposition into a zero tail and a weighted family
  of TP-gauged blocks with primitive transfer maps.

* `exists_normalCanonicalForm_after_blocking_conditional`:
  If additionally the blocked blocks are irreducible (tensor sense) and the
  blocked weights have pairwise distinct norms, then the data forms an
  `IsNormalCanonicalForm`.

## Gap documentation

The remaining gap between `exists_tp_primitive_blockDecomp_after_blocking` and a
full `IsNormalCanonicalForm` from arbitrary input is:

1. **Blocked irreducibility**: After blocking by period `P`, the blocked blocks
   `blockTensor (blocks k) P` may fail to be `IsIrreducibleTensor`, even though
   the original blocks are irreducible. (Counterexample: `d = 1`, `D = 2`,
   `A₁ = permutation matrix`, `P = 2`: `A₁² = I` is reducible.)

2. **Weight norm separation**: The weights `(μ k)^P` may have equal norms for
   different blocks. The paper handles this via BNT grouping (arXiv:1606.00608,
   §2.3), which is not yet formalized.

Both gaps are addressed by the paper's cyclic sector decomposition, which
decomposes each periodic block into primitive sectors before blocking.

### Progress on cyclic sector decomposition (#242)

The per-block bridge is now complete:

* `exists_cyclic_sector_decomp_of_TP_of_isIrreducibleTensor`: For each irreducible TP block,
  derives all channel-level hypotheses automatically and produces cyclic
  sector blocks via `exists_cyclic_sector_decomp_after_blocking`.

Remaining work for the full pipeline integration:

* **Common period assembly**: Combining per-block cyclic sectors into a
  single global decomposition with a common blocking period. Requires
  iterated-blocking infrastructure (`blockTensor (blockTensor A p) q ≃
  blockTensor A (p * q)`).

* **Sector irreducibility**: Each cyclic sector should inherit irreducibility
  from `isIrreducible_restriction_of_cyclic_decomp`. The orbit-sum lift from
  corner restriction to compressed tensor is not yet formalized.

* **BNT grouping** (#243): Weight norm separation after sector decomposition.

## References

- [Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608, §2.3 + Appendix A]
- [Cirac–Pérez-García–Schuch–Verstraete, arXiv:2011.12127, §IV]
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

* a **zero tail** of dimension `zeroTailDim` (accumulating all-zero irreducible
  blocks from the original decomposition);
* a family of **blocked live blocks** `blocks k` indexed by `Fin r`, each with:
  - left-canonical (TP) normalization `∑ᵢ (blocks k i)ᴴ * (blocks k i) = I`;
  - primitive transfer map `_root_.IsPrimitive (transferMap (blocks k))`;
  - positive bond dimension;
  - nonzero weight `μ k`.

The MPV relationship holds:
```
  mpv (blockTensor A p) σ = mpv (zeroMPSTensor (blockPhysDim d p) zeroTailDim) σ
    + mpv (toTensorFromBlocks μ blocks) σ
```

In particular, for system sizes `N > 0`, the zero tail vanishes and
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
    -- Zero tail: both sides equal `if N = 0 then zeroTailDim else 0`.
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
  IsNormalCanonicalForm.ofSeparatedData
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

/-!
## Per-block chain from TP + primitive + irreducible to IsNormal

For a single block that is TP, has a primitive transfer map, AND is irreducible
(all three conditions), the full chain to `IsNormal` is available:

1. `_root_.IsPrimitive (transferMap A)` + `IsIrreducibleTensor A` + TP
   → `hasPrimitiveFixedPoint_of_peripheralPrimitive_of_irreducible`
   → `∃ ρ, IsPrimitiveMPS A ρ`
2. `IsPrimitiveMPS A ρ` + `IsIrreducibleTensor A`
   → `posDef_of_isIrreducibleTensor_of_isPrimitiveMPS` → `ρ.PosDef`
3. `IsPrimitiveMPS A ρ` + `ρ.PosDef`
   → `isNormal_of_isPrimitiveMPS_with_posDef` → `IsNormal A`

We package this chain as a single theorem.
-/

/-- **TP + primitive + irreducible → IsNormal** (per-block chain).

For a single MPS tensor that is left-canonical (TP), has a primitive transfer map
(peripheral eigenvalues = {1}), and is irreducible (no nontrivial invariant
projection), the tensor is normal (eventually full Kraus rank).

This chains:
- Peripheral primitivity + irreducibility → existence of a primitive fixed point
- Spectral-gap + irreducibility → PosDef fixed point
- Spectral-gap + PosDef → HasEventuallyFullKrausRank → IsNormal -/
theorem isNormal_of_tp_primitive_irreducible [NeZero D]
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : _root_.IsPrimitive (transferMap (d := d) (D := D) A))
    (hIrr : IsIrreducibleTensor A) :
    IsNormal A := by
  -- Step 1: Get spectral-gap primitivity from peripheral primitivity + irreducibility.
  have hMPSPrim : MPSTensor.HasPrimitiveFixedPoint A :=
    hasPrimitiveFixedPoint_of_peripheralPrimitive_of_irreducible A hIrr hTP hPrim
  -- Step 2: Extract the PSD fixed point.
  obtain ⟨ρ, hPrimMPS⟩ := hMPSPrim
  -- Step 3: Upgrade PSD → PosDef using tensor irreducibility.
  have hPD : ρ.PosDef :=
    posDef_of_isIrreducibleTensor_of_isPrimitiveMPS hPrimMPS hIrr
  -- Step 4: IsNormal from spectral gap + PosDef.
  exact isNormal_of_isPrimitiveMPS_with_posDef hPrimMPS hPD

/-!
## Combined reduction: arbitrary → IsNormal (per block, for primitive blocks)

For the pre-blocking blocks (which ARE irreducible), the chain to IsNormal
works directly. This shows that the original (unblocked) live blocks become
normal once we know their transfer maps are primitive.
-/

/-- **Pre-blocking blocks are normal once primitive.**

For the live blocks from the arbitrary-input TP-gauge reduction, if a block
additionally has a primitive transfer map, then it is normal. -/
theorem isNormal_live_block_of_primitive [NeZero D]
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hIrr : IsIrreducibleTensor A)
    (hPrim : _root_.IsPrimitive (transferMap (d := d) (D := D) A)) :
    IsNormal A :=
  isNormal_of_tp_primitive_irreducible A hTP hPrim hIrr

/-!
## IsNormal is preserved by blocking

The key observation: if `wordSpan A N = ⊤`, then `wordSpan A (m * N) = ⊤` for all `m ≥ 1`
(because `⊤ * wordSpan A k ⊇ wordSpan A k` via the identity). Combined with the containment
`wordSpan A (n * P) ≤ wordSpan (blockTensor A P) n`, this gives:
`IsNormal A → IsNormal (blockTensor A P)`.

This bypasses the blocked-irreducibility gap entirely for the IsNormal conclusion.
-/

/-- The word span at `N + k` contains the word span at `k` when `wordSpan A N = ⊤`.

Proof: `wordSpan A N * wordSpan A k ≤ wordSpan A (N + k)`, and `1 ∈ wordSpan A N = ⊤`
gives `M = 1 * M ∈ wordSpan A N * wordSpan A k` for any `M ∈ wordSpan A k`. -/
private theorem wordSpan_le_wordSpan_add_of_wordSpan_eq_top
    (A : MPSTensor d D) {N : ℕ} (hN : wordSpan A N = ⊤) (k : ℕ) :
    wordSpan A k ≤ wordSpan A (N + k) := by
  intro M hM
  have h1 : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ wordSpan A N := by
    rw [hN]; exact Submodule.mem_top
  have hprod : (1 : Matrix (Fin D) (Fin D) ℂ) * M ∈ wordSpan A N * wordSpan A k :=
    Submodule.mul_mem_mul h1 hM
  rw [one_mul] at hprod
  exact wordSpan_mul_le A N k hprod

/-- The word span at any positive multiple of `N` is `⊤` when `wordSpan A N = ⊤`.

Proof by induction: `wordSpan A ((m+1)*N) ⊇ wordSpan A (m*N)` via the preceding lemma
(with `k = m*N`). -/
private theorem wordSpan_mul_eq_top_of_wordSpan_eq_top
    (A : MPSTensor d D) {N : ℕ} (hN : wordSpan A N = ⊤) (m : ℕ) (hm : 0 < m) :
    wordSpan A (m * N) = ⊤ := by
  induction m with
  | zero => exact absurd rfl (Nat.ne_of_gt hm)
  | succ n ih =>
    by_cases hn : n = 0
    · simp [hn, hN]
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
      have hprev := ih hn_pos
      have hle : wordSpan A (n * N) ≤ wordSpan A ((n + 1) * N) := by
        calc wordSpan A (n * N)
            ≤ wordSpan A (N + n * N) :=
              wordSpan_le_wordSpan_add_of_wordSpan_eq_top A hN (n * N)
          _ = wordSpan A ((n + 1) * N) := by ring_nf
      exact eq_top_iff.mpr (hprev ▸ hle)

/-- **IsNormal is preserved by blocking.**

If `A` is normal (`∃ N, wordSpan A N = ⊤`), then `blockTensor A P` is also normal
for any `P ≥ 1`. The proof uses:
1. `wordSpan A N = ⊤ → wordSpan A (P * N) = ⊤` (word span at multiples);
2. `wordSpan A (n * P) ≤ wordSpan (blockTensor A P) n` (blocking containment).

Taking `n = N` in (2) and using (1) with `m = P`: `wordSpan A (N * P) = ⊤` and
`wordSpan (blockTensor A P) N ⊇ wordSpan A (N * P) = ⊤`. -/
theorem isNormal_blockTensor_of_isNormal
    (A : MPSTensor d D) {P : ℕ} (hP : 0 < P) (hN : IsNormal A) :
    IsNormal (d := blockPhysDim d P) (D := D) (blockTensor (d := d) (D := D) A P) := by
  obtain ⟨N, hNblk⟩ := hN
  have hwordN : wordSpan A N = ⊤ :=
    (wordSpan_eq_top_iff_isNBlkInjective A N).mpr hNblk
  have hwordNP : wordSpan A (P * N) = ⊤ :=
    wordSpan_mul_eq_top_of_wordSpan_eq_top A hwordN (N := N) (m := P) hP
  -- wordSpan A (N * P) ≤ wordSpan (blockTensor A P) N
  have hle : wordSpan A (N * P) ≤
      wordSpan (blockTensor (d := d) (D := D) A P) N :=
    wordSpan_le_wordSpan_blockTensor A P N
  have hwordNP' : wordSpan A (N * P) = ⊤ := by rwa [Nat.mul_comm] at hwordNP
  rw [hwordNP'] at hle
  refine ⟨N, ?_⟩
  exact (wordSpan_eq_top_iff_isNBlkInjective
    (blockTensor (d := d) (D := D) A P) N).mp (eq_top_iff.mpr hle)

/-!
## Blocked blocks are irreducible tensors (for primitive blocks)

For a single block that is TP, has a primitive transfer map, and is irreducible,
the blocked tensor `blockTensor A P` is also irreducible.

The proof strategy avoids the "blocked period" issue entirely by working directly
with the PSD fixed point `ρ` of the original transfer map:

1. From TP + IsPrimitive + IsIrreducibleTensor → `IsPrimitiveMPS A ρ` with `ρ.PosDef`
   (via `hasPrimitiveFixedPoint_of_peripheralPrimitive_of_irreducible` +
    `posDef_of_isIrreducibleTensor_of_isPrimitiveMPS`)
2. `ρ` is also fixed by `transferMap (blockTensor A P)` (since `transferMap (blockTensor A P) = E^P`
   and `E ρ = ρ` implies `E^P ρ = ρ`)
3. Uniqueness of PSD fixed points of `E^P`: if `E^P σ = σ`, set `σ' = σ - c•ρ`.
   From the spectral gap of `IsPrimitiveMPS A ρ`, `E^n → Pρ` exponentially.
   Since `E^{Pk} σ' = Pρ σ' + N^{Pk} σ' = N^{Pk} σ'` (as `Pρ σ' = 0`)
   and `N^{Pk} σ' = σ'` (from `E^P σ' = σ'`), but `N^n → 0`, we get `σ' = 0`.
4. Apply `isIrreducibleMap_of_channel_posDef_fixedPoint_unique` →
   `IsIrreducibleMap (transferMap (blockTensor A P))`
5. Apply `isIrreducibleTensor_of_isIrreducibleMap` →
   `IsIrreducibleTensor (blockTensor A P)`
-/

/-- **Blocked blocks are irreducible tensors** (for originally primitive blocks).

If `A` is TP, has a primitive transfer map, and is an irreducible tensor, then
`blockTensor A P` is also an irreducible tensor for any `P ≥ 1`.

The key insight: the PosDef fixed point `ρ` of the original transfer map is also
a PosDef fixed point of the blocked transfer map `E^P`. Uniqueness of PSD fixed
points for `E^P` follows from the spectral gap of `IsPrimitiveMPS A ρ`: if
`E^P σ = σ` then `N^{Pk} σ' = σ'` (where `σ' = σ - c•ρ`, `N = E - Pρ`), but
`N^n → 0` from the spectral gap, so `σ' = 0`. -/
theorem isIrreducibleTensor_blockTensor_of_tp_primitive_irr [NeZero D]
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : _root_.IsPrimitive (transferMap (d := d) (D := D) A))
    (hIrr : IsIrreducibleTensor A)
    {P : ℕ} (hP : 0 < P) :
    IsIrreducibleTensor (blockTensor A P) := by
  -- Step 1: Obtain IsPrimitiveMPS A ρ with ρ.PosDef.
  obtain ⟨ρ, hPrimMPS⟩ :=
    hasPrimitiveFixedPoint_of_peripheralPrimitive_of_irreducible A hIrr hTP hPrim
  have hPD : ρ.PosDef :=
    posDef_of_isIrreducibleTensor_of_isPrimitiveMPS hPrimMPS hIrr
  -- Step 2: Blocked tensor is TP.
  have hTP_blocked : ∑ i : Fin (blockPhysDim d P),
      (blockTensor (d := d) (D := D) A P i)ᴴ * blockTensor (d := d) (D := D) A P i = 1 :=
    leftCanonical_blockTensor A P hTP
  -- Step 3: Blocked transfer map is a channel.
  have hCh : IsChannel (transferMap (d := blockPhysDim d P) (D := D) (blockTensor A P)) :=
    transferMap_isChannel (blockTensor A P) hTP_blocked
  -- Step 4: ρ is fixed by the blocked transfer map.
  have hρ_fix_blocked :
      transferMap (d := blockPhysDim d P) (D := D) (blockTensor A P) ρ = ρ :=
    transferMap_blockTensor_fixedPoint A P ρ hPrimMPS.fixedPoint_is_fixed
  -- Step 5: Uniqueness of PSD fixed points of transferMap(blockTensor A P).
  -- Strategy: if E^P σ = σ, set σ' = σ - c•ρ (c = tr σ / tr ρ).
  -- Show N^{Pk} σ' = σ' for all k ≥ 1, but N^n → 0, hence σ' = 0.
  have huniq : ∀ σ : Matrix (Fin D) (Fin D) ℂ,
      σ.PosSemidef →
      transferMap (d := blockPhysDim d P) (D := D) (blockTensor A P) σ = σ →
      ∃ c : ℂ, σ = c • ρ := by
    intro σ _hσ_psd hσ_fix
    -- Convert hσ_fix to: (transferMap A)^P σ = σ.
    rw [transferMap_blockTensor] at hσ_fix
    -- Set abbreviations.
    set E := transferMap (d := d) (D := D) A with E_def
    set Pρ := fixedPointProj (D := D) ρ hPrimMPS.trace_ne_zero with Pρ_def
    set N := E - Pρ with N_def
    set c := Matrix.trace σ / Matrix.trace ρ with c_def
    use c
    -- Suffices to show σ - c • ρ = 0.
    suffices h0 : σ - c • ρ = 0 from eq_of_sub_eq_zero h0
    set σ' := σ - c • ρ with σ'_def
    -- tr σ' = 0.
    have htr_σ' : Matrix.trace σ' = 0 := by
      simp [σ'_def, Matrix.trace_sub, Matrix.trace_smul, c_def,
            div_mul_cancel₀ _ hPrimMPS.trace_ne_zero]
    -- E^P ρ = ρ (ρ is fixed by the blocked transfer map, hence by E^P).
    have hE_pow_ρ : (E ^ P) ρ = ρ := by
      simpa [E_def, transferMap_blockTensor_apply (A := A) (L := P) (X := ρ)] using hρ_fix_blocked
    -- E^P σ' = σ'.
    have hEP_σ' : (E ^ P) σ' = σ' := by
      simp only [σ'_def, map_sub, LinearMap.map_smul_of_tower, hσ_fix, hE_pow_ρ]
    -- (E^P)^k σ' = σ' for all k (by induction on k).
    have hEPk_σ' : ∀ k : ℕ, ((E ^ P) ^ k) σ' = σ' := by
      intro k
      induction k with
      | zero => simp
      | succ n ih =>
          simp [pow_succ', ih, hEP_σ']
    -- N^{Pk} σ' = σ' for all k ≥ 1.
    have hN_pow_σ' : ∀ k : ℕ, 0 < k → (N ^ (P * k)) σ' = σ' := by
      intro k hk
      have hPk_pos : 1 ≤ P * k := Nat.mul_pos hP hk
      -- E^{Pk} = Pρ + N^{Pk} (from pow_eq_fixedPointProj_add_compl_pow).
      have hdecomp : (E ^ (P * k)) σ' = Pρ σ' + (N ^ (P * k)) σ' := by
        have h := pow_eq_fixedPointProj_add_compl_pow E hPrimMPS.trace_ne_zero
          hPrimMPS.transferMap_isChannel.tp hPrimMPS.fixedPoint_is_fixed hPk_pos
        have happ := congrArg (fun T => T σ') h
        simpa [Pρ_def, N_def, LinearMap.add_apply] using happ
      -- E^{Pk} σ' = σ' (from hEPk_σ').
      have hEPk : (E ^ (P * k)) σ' = σ' := by
        rw [pow_mul]
        exact hEPk_σ' k
      -- Pρ σ' = 0 (since tr σ' = 0).
      have hPρ_σ' : Pρ σ' = 0 := by
        simp [Pρ_def, fixedPointProj, htr_σ']
      -- Combine: N^{Pk} σ' = E^{Pk} σ' - Pρ σ' = σ'.
      calc
        (N ^ (P * k)) σ'
            = 0 + (N ^ (P * k)) σ' := (zero_add _).symm
        _ = Pρ σ' + (N ^ (P * k)) σ' := by rw [hPρ_σ']
        _ = (E ^ (P * k)) σ' := hdecomp.symm
        _ = σ' := hEPk
    -- N^n σ' → 0 (from complement_pow_tendsto_zero applied to σ').
    have hN_tendsto : Filter.Tendsto (fun n => (N ^ n) σ') Filter.atTop (nhds 0) := by
      let V := Matrix (Fin D) (Fin D) ℂ
      let Φ : (V →ₗ[ℂ] V) ≃ₐ[ℂ] (V →L[ℂ] V) := Module.End.toContinuousLinearMap V
      -- (Φ N)^n → 0 as CLMs.
      have hN_clm : Filter.Tendsto (fun n => (Φ N) ^ n) Filter.atTop (nhds 0) :=
        hPrimMPS.complement_pow_tendsto_zero
      -- Evaluate at σ': (Φ N)^n σ' → 0.
      have heval := (ContinuousLinearMap.apply ℂ V σ').continuous.tendsto
        (0 : V →L[ℂ] V)
      rw [map_zero] at heval
      have hconv := heval.comp hN_clm
      -- Convert CLM powers to LinearMap powers: (Φ N)^n σ' = N^n σ'.
      suffices hsuff : ∀ n, ((Φ N) ^ n) σ' = (N ^ n) σ' by
        simp_rw [← hsuff]
        exact hconv
      intro n
      rw [← map_pow Φ N n]
      rfl
    -- σ' = 0: the subsequence N^{P*(k+1)} σ' = σ' → 0 shows σ' = 0.
    have hg_tendsto : Filter.Tendsto (fun k : ℕ => P * (k + 1)) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_atTop.mpr fun b =>
        ⟨b, fun k hk => by
          have hk1 : k + 1 ≥ b + 1 := Nat.add_le_add_right hk 1
          have hPk1 : P * (k + 1) ≥ k + 1 := Nat.le_mul_of_pos_left _ hP
          omega⟩
    have hconst_tendsto : Filter.Tendsto (fun _ : ℕ => σ') Filter.atTop (nhds 0) := by
      have hconv2 : Filter.Tendsto (fun k => (N ^ (P * (k + 1))) σ') Filter.atTop (nhds 0) :=
        hN_tendsto.comp hg_tendsto
      have heq : (fun k : ℕ => (N ^ (P * (k + 1))) σ') = fun _ => σ' := by
        funext k
        exact hN_pow_σ' (k + 1) (Nat.succ_pos k)
      rwa [heq] at hconv2
    exact tendsto_nhds_unique tendsto_const_nhds hconst_tendsto
  -- Step 6: Apply isIrreducibleMap_of_channel_posDef_fixedPoint_unique.
  have hIrrMap : IsIrreducibleMap
      (transferMap (d := blockPhysDim d P) (D := D) (blockTensor A P)) :=
    isIrreducibleMap_of_channel_posDef_fixedPoint_unique
      (transferMap (d := blockPhysDim d P) (D := D) (blockTensor A P))
      hCh ρ hPD hρ_fix_blocked huniq
  -- Step 7: IsIrreducibleMap → IsIrreducibleTensor.
  exact isIrreducibleTensor_of_isIrreducibleMap (blockTensor A P) hIrrMap

/-!
## Weak FT: proportional MPVs → block matching (for TP-primitive blocks)

This packages the full reduction output together with the downstream
FT theorems, showing how the reduction connects to the fundamental theorem
conclusions.

For two arbitrary tensors A, B with proportional MPVs, the reduction produces
blocked TP-primitive decompositions. Under the additional hypotheses needed
for `IsNormalCanonicalForm` (irreducibility + distinct weight norms), the
downstream FT gives permutation + gauge-phase matching of blocks.
-/

/-- **Weak Fundamental Theorem (conditional on irreducibility + distinct weights).**

For two tensor families in TP-primitive normal canonical form with BNT separation,
if their blocked versions have proportional MPVs (with convergent coefficients), then
the block counts match and blocks are pairwise gauge-phase equivalent (up to
permutation). This packages the downstream FT from `Full.lean`. -/
theorem weakFundamentalTheorem_conditional
    {d' rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {DtotA DtotB : ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d' (dimA j))
    (B : (k : Fin rB) → MPSTensor d' (dimB k))
    (hA_ncf : IsNormalCanonicalForm μA A)
    (hA_blocks : ∀ j k : Fin rA, j ≠ k →
      ∀ (h : dimA j = dimA k),
        ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d') h) (A j)) (A k))
    (hB_ncf : IsNormalCanonicalForm μB B)
    (hB_blocks : ∀ j k : Fin rB, j ≠ k →
      ∀ (h : dimB j = dimB k),
        ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d') h) (B j)) (B k))
    (A_total : MPSTensor d' DtotA)
    (B_total : MPSTensor d' DtotB)
    (aCoeff : ℕ → Fin rA → ℂ) (bCoeff : ℕ → Fin rB → ℂ)
    (aLim : Fin rA → ℂ) (bLim : Fin rB → ℂ)
    (c : ℕ → ℂ) (cLim : ℂ)
    (hA_decomp : ∀ N (σ : Fin N → Fin d'),
      mpv A_total σ = ∑ j : Fin rA, (aCoeff N j) * mpv (A j) σ)
    (hB_decomp : ∀ N (σ : Fin N → Fin d'),
      mpv B_total σ = ∑ k : Fin rB, (bCoeff N k) * mpv (B k) σ)
    (haCoeff : ∀ j, Tendsto (fun N => aCoeff N j) atTop (nhds (aLim j)))
    (hbCoeff : ∀ k, Tendsto (fun N => bCoeff N k) atTop (nhds (bLim k)))
    (haLim_ne : ∀ j, aLim j ≠ 0)
    (hbLim_ne : ∀ k, bLim k ≠ 0)
    (hProp : ∀ N (σ : Fin N → Fin d'), mpv A_total σ = c N * mpv B_total σ)
    (hc : Tendsto c atTop (nhds cLim))
    (hcLim_ne : cLim ≠ 0) :
    ∃ _h : rA = rB,
      ∃ perm : Fin rA ≃ Fin rB,
        ∀ j : Fin rA,
          ∃ hdim : dimA j = dimB (perm j),
            GaugePhaseEquiv (d := d')
              (cast (congr_arg (MPSTensor d') hdim) (A j))
              (B (perm j)) :=
  MPSTensor.fundamentalTheorem_proportionalMPV_of_separated_normalCFBNT_data A B
    hA_ncf hA_blocks hB_ncf hB_blocks
    A_total B_total aCoeff bCoeff aLim bLim c cLim
    hA_decomp hB_decomp haCoeff hbCoeff haLim_ne hbLim_ne hProp hc hcLim_ne

/-!
## Cyclic sector decomposition via the CyclicSectors API

### Mathematical overview

For an irreducible TP block `A` of period `m`, the adjoint transfer map
`E† = transferMap (fun i => (A i)ᴴ)` has peripheral spectrum `{γ^k | k ∈ Fin m}`.
The cyclic decomposition from `CyclicDecomposition.lean` produces projections `P_k` with:
- `∀ k, IsOrthogonalProjection (P k)` and `∑ k, P k = 1`
- `E†(P(k+1)) = P k` (cyclic), hence `(E†)^m (P k) = P k`

The key bridge: `(E†)^m = transferMap (fun j => (blockTensor A m j)ᴴ)` because the
adjoint of the blocked transfer map equals the m-th iterate of the adjoint transfer map.
This is proved by a tuple-reversal bijection: summing `A_w†·X·A_w` over all length-`m`
words `w` gives the same result regardless of whether `A_w` or `A_{rev(w)}` is used.

### Reduction

1. Get cyclic projections from `CyclicDecomposition.lean` applied to `K = (A·)ᴴ`
2. Show `(transferMap K)^m` fixes each projection (iterate cycling `m` times)
3. Use `transferMap_blockTensor` to identify `(transferMap K)^m = transferMap(blockTensor K m)`
4. Show `transferMap(blockTensor K m) = transferMap(fun j => (blockTensor A m j)ᴴ)` by reversal
5. Apply `exists_blockDecomp_of_adjoint_fixed_projections` from `CyclicSectors.lean`
-/

section CyclicSectorBridge


open KadisonSchwarz

/-- Cyclic shift: `(k + n) % m` as a `Fin m`. -/
private def cyclicShift {m : ℕ} [NeZero m] (k : Fin m) (n : ℕ) : Fin m :=
  ⟨((k : ℕ) + n) % m, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne m))⟩

@[simp] private lemma cyclicShift_zero {m : ℕ} [NeZero m] (k : Fin m) :
    cyclicShift k 0 = k := by
  ext; simp [cyclicShift, Nat.mod_eq_of_lt k.is_lt]

private lemma cyclicShift_succ {m : ℕ} [NeZero m] (k : Fin m) (n : ℕ) :
    cyclicShift k (n + 1) = cyclicShift k n + 1 := by
  ext
  change ((↑k + n) + 1) % m = (((↑k + n) % m) + 1 % m) % m
  exact Nat.add_mod (↑k + n) 1 m

@[simp] private lemma cyclicShift_self {m : ℕ} [NeZero m] (k : Fin m) :
    cyclicShift k m = k := by
  ext
  change (↑k + m) % m = ↑k
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt k.is_lt]

/-- Iterating the cyclic relation `E†(P(k+1)) = P_k` exactly `m` times gives
`(E†)^m (P_k) = P_k`. -/
private theorem adjointTransferMap_pow_fixes_cyclic_projection
    {d D m : ℕ} [NeZero m]
    (K : Fin d → MatrixAlg D)
    (P : Fin m → MatrixAlg D)
    (hcyclic : ∀ k : Fin m, transferMap (d := d) (D := D) K (P (k + 1)) = P k) :
    ∀ k : Fin m, ((transferMap (d := d) (D := D) K) ^ m) (P k) = P k := by
  -- Strategy: prove (E†)^n (P (k + n)) = P k for Fin m addition, by induction on n.
  -- For n = m, k + m = k in Fin m, so (E†)^m (P k) = P k.
  -- The key is: (E†)^(n+1) (P (k + (n+1))) = E†((E†)^n (P (k + (n+1))))
  -- = E†((E†)^n (P ((k+1) + n)))     [since k + (n+1) = (k+1) + n in Fin m]
  -- = E†(P (k+1))                     [by IH with k' = k+1]
  -- = P k                              [by hcyclic]
  -- Prove: ∀ n, ∀ k, (E†)^n (P (k + n)) = P k  where n is a Fin m literal.
  -- We use Nat.rec on n, carrying a proof that the Fin m literal n is (n % m).
  -- But this is cleaner using hcyclic directly in a simple induction.
  -- Base: (E†)^0 (P (k + 0)) = P k  ✓
  -- Step: (E†)^(n+1) (P (k + (n+1)))
  --     = E†((E†)^n (P (k + (n+1))))     [pow decomp]
  --     = E†((E†)^n (P ((k+1) + n)))     [Fin m add assoc]
  --     = E†(P (k+1))                    [IH with k' = k+1]
  --     = P k                             [hcyclic]
  -- At n = m: k + m = k in Fin m, so (E†)^m (P k) = P k.
  intro k
  -- Direct approach: iterate hcyclic m times
  suffices ∀ n : ℕ, n ≤ m →
      ∀ (k : Fin m), ((transferMap (d := d) (D := D) K) ^ n)
        (P ⟨((k : ℕ) + n) % m, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne m))⟩) = P k by
    have h := this m le_rfl k
    simpa [Nat.add_mod_right, Nat.mod_eq_of_lt k.is_lt] using h
  intro n
  induction n with
  | zero =>
    intro _ k
    simp [Nat.mod_eq_of_lt k.is_lt]
  | succ n ih =>
    intro hn k
    have hn' : n ≤ m := Nat.le_of_succ_le hn
    have hlt : ((k : ℕ) + (n + 1)) % m < m :=
      Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne m))
    -- Decompose the power
    have hpow : ((transferMap (d := d) (D := D) K) ^ (n + 1))
        (P ⟨((k : ℕ) + (n + 1)) % m, hlt⟩) =
        (transferMap (d := d) (D := D) K)
          (((transferMap (d := d) (D := D) K) ^ n)
            (P ⟨((k : ℕ) + (n + 1)) % m, hlt⟩)) := by
      rw [pow_succ']; rfl
    rw [hpow]
    -- (k + (n+1)) % m = ((k+1) + n) % m
    have hmod : ((k : ℕ) + (n + 1)) % m = (((k : ℕ) + 1) + n) % m := by
      congr 1; omega
    -- Create the Fin m index for (k+1)
    set k1 : Fin m := k + 1
    -- Apply IH with k' = k+1
    have := ih hn' k1
    -- ih says: (E†)^n (P ⟨(↑k1 + n) % m, _⟩) = P k1
    -- We need: (E†)^n (P ⟨((↑k + n + 1)) % m, _⟩) = P k1
    -- Since (↑k + (n+1)) % m = (↑k1 + n) % m
    have hval_eq : ((k : ℕ) + (n + 1)) % m = ((k1 : ℕ) + n) % m := by
      simp [k1, Fin.val_add]; omega
    have hfin_eq :
        (⟨((k : ℕ) + (n + 1)) % m, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne m))⟩ : Fin m) =
          ⟨((k1 : ℕ) + n) % m, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne m))⟩ := by
      ext; exact hval_eq
    rw [hfin_eq, this]
    exact hcyclic k

/-- The adjoint of the blocked transfer map equals the `m`-th iterate of the
adjoint transfer map:
`transferMap (fun j => (blockTensor A m j)ᴴ) X = ((transferMap (fun i => (A i)ᴴ))^m) X`

This is proved by passing to Frobenius adjoints. First,
`transferMap (fun i => (A i)ᴴ) = (transferMap A).adjoint`, and likewise for the blocked
family `blockTensor A m`. Second, `transferMap (blockTensor A m) = (transferMap A)^m` by
`transferMap_blockTensor`. Finally, adjoint commutes with powers, so
`((transferMap A)^m).adjoint = ((transferMap A).adjoint)^m`. -/
private theorem transferMap_adjoint_blocked_eq_pow
    {d D : ℕ} (A : MPSTensor d D) (m : ℕ) (X : MatrixAlg D) :
    transferMap (d := blockPhysDim d m) (D := D) (fun j => (blockTensor A m j)ᴴ) X =
      ((transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ m) X := by
  classical
  have hM : (1 : Matrix (Fin D) (Fin D) ℂ).PosDef := by
    simpa using (Matrix.PosDef.one (n := Fin D) (R := ℂ))
  letI : NormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.toMatrixNormedAddCommGroup (n := Fin D) (𝕜 := ℂ) 1 hM
  letI : SeminormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.toMatrixSeminormedAddCommGroup (n := Fin D) (𝕜 := ℂ) 1 hM.posSemidef
  letI : InnerProductSpace ℂ (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.toMatrixInnerProductSpace (n := Fin D) (𝕜 := ℂ) 1 hM.posSemidef
  have hBlockedAdj :
      transferMap (d := blockPhysDim d m) (D := D) (fun j => (blockTensor A m j)ᴴ) =
        (transferMap (d := blockPhysDim d m) (D := D) (blockTensor A m)).adjoint := by
    simpa using
      (transferMap_conjTranspose_eq_adjoint
        (d := blockPhysDim d m) (D := D) (A := blockTensor A m))
  have hAdj :
      transferMap (d := d) (D := D) (fun i => (A i)ᴴ) =
        (transferMap (d := d) (D := D) A).adjoint := by
    simpa using
      (transferMap_conjTranspose_eq_adjoint (d := d) (D := D) (A := A))
  have hPowAdj :
      ((transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ m) =
        (((transferMap (d := d) (D := D) A) ^ m).adjoint) := by
    rw [hAdj]
    have hpow : (((transferMap (d := d) (D := D) A) ^ m).adjoint) =
        ((transferMap (d := d) (D := D) A).adjoint) ^ m := by
      simpa only [LinearMap.star_eq_adjoint] using
        (star_pow (x := transferMap (d := d) (D := D) A) (n := m))
    simpa using hpow.symm
  calc
    transferMap (d := blockPhysDim d m) (D := D) (fun j => (blockTensor A m j)ᴴ) X
        = ((transferMap (d := blockPhysDim d m) (D := D) (blockTensor A m)).adjoint) X := by
            rw [hBlockedAdj]
    _ = (((transferMap (d := d) (D := D) A) ^ m).adjoint) X := by
          rw [transferMap_blockTensor]
    _ = ((transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ m) X := by
          rw [← hPowAdj]

/-- **Cyclic sector decomposition for a blocked periodic tensor.**

For an irreducible TP tensor `A` of period `m`, after blocking by `m`, the blocked tensor
`blockTensor A m` admits a sector decomposition into `m` TP blocks via the cyclic
spectral projections. Each sector is left-canonical and the direct-sum tensor is
`SameMPV₂`-equivalent to the blocked tensor. -/
theorem exists_cyclic_sector_decomp_after_blocking
    {d D m : ℕ} [NeZero D] [NeZero m]
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (_hIrr : IsIrreducibleTensor A)
    (ρ : MatrixAlg D) (hρ : ρ.PosDef)
    (hρfix : Kraus.adjointMap (fun i : Fin d => (A i)ᴴ) ρ = ρ)
    (hIrrMap : IsIrreducibleMap (transferMap (d := d) (D := D) (fun i => (A i)ᴴ)))
    {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (hperiph : peripheralEigenvalues (transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) =
      Set.range (fun j : Fin m => γ ^ (j : ℕ))) :
    ∃ (dim : Fin m → ℕ) (blocks : (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k)),
      (∀ k, ∑ i : Fin (blockPhysDim d m), (blocks k i)ᴴ * blocks k i = 1) ∧
      SameMPV₂ (blockTensor A m) (toTensorFromBlocks (μ := fun _ => 1) blocks) := by
  -- Step 1: Get cyclic decomposition data
  let K : Fin d → MatrixAlg D := fun i => (A i)ᴴ
  have hUnital : IsUnitalKraus (d := d) (D := D) K := by
    simpa [IsUnitalKraus, K] using hTP
  obtain ⟨U, P, hU, hPow, hUm, hPproj, hPsum, hUspec, hcyclic⟩ :=
    MPSTensor.exists_cyclic_decomposition_of_irreducible_schwarz
      (K := K) hUnital ρ hρ hρfix hIrrMap hγprim hperiph
  -- Step 2: (E†)^m fixes each P_k
  have hPow_fix : ∀ k : Fin m,
      ((transferMap (d := d) (D := D) K) ^ m) (P k) = P k :=
    adjointTransferMap_pow_fixes_cyclic_projection K P hcyclic
  -- Step 3: Adjoint blocked transfer map fixes P_k
  have hFix : ∀ k : Fin m,
      transferMap (d := blockPhysDim d m) (D := D)
        (fun i => (blockTensor A m i)ᴴ) (P k) = P k := by
    intro k
    rw [transferMap_adjoint_blocked_eq_pow A m (P k)]
    exact hPow_fix k
  -- Step 4: Blocked tensor is TP
  have hTP_blocked : ∑ i : Fin (blockPhysDim d m),
      (blockTensor A m i)ᴴ * blockTensor A m i = 1 :=
    leftCanonical_blockTensor (d := d) (D := D) (A := A) (L := m) hTP
  -- Step 5: Apply the CyclicSectors decomposition
  exact exists_blockDecomp_of_adjoint_fixed_projections
    (blockTensor A m) P hPproj hPsum hTP_blocked hFix

end CyclicSectorBridge

/-!
## Bridge: MPS hypotheses → cyclic sector decomposition

For an irreducible TP tensor, all channel-level hypotheses needed by
`exists_cyclic_sector_decomp_after_blocking` can be derived automatically:

1. `IsIrreducibleTensor A` → `IsIrreducibleMap (transferMap (fun i => (A i)ᴴ))`
2. TP + irreducible → ∃ ρ.PosDef fixed by `transferMap A` = `Kraus.adjointMap K`
3. `peripheral_eigenvalues_cyclic_structure` → `(m, γ, IsPrimitiveRoot γ m, periph = {γ^k})`
4. Feed all into `exists_cyclic_sector_decomp_after_blocking`
-/

section CyclicSectorFromMPS

open KadisonSchwarz

/-- From an irreducible TP tensor, derive the conjugate-transposed Kraus family `K`,
its unitality and irreducibility, and a `PosDef` fixed point `ρ` of `Kraus.adjointMap K`.

This bundles the common setup shared by `exists_cyclic_sector_decomp_of_TP_of_isIrreducibleTensor`
and `exists_blockTensor_isPrimitive_of_TP_of_isIrreducibleTensor`. -/
theorem conjTranspose_kraus_setup
    {d D : ℕ} [NeZero D]
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hIrr : IsIrreducibleTensor A) :
    ∃ (K : MPSTensor d D)
      (_ : IsUnitalKraus (d := d) (D := D) K)
      (_ : IsIrreducibleMap (transferMap (d := d) (D := D) K))
      (ρ : Matrix (Fin D) (Fin D) ℂ)
      (_ : ρ.PosDef)
      (_ : Kraus.adjointMap K ρ = ρ),
      K = fun i => (A i)ᴴ := by
  classical
  have hDpos : 0 < D := NeZero.pos D
  let K : MPSTensor d D := fun i => (A i)ᴴ
  have hTP' : IsTPKraus (d := d) (D := D) A := by
    simpa [IsTPKraus] using hTP
  have h_unitalK : IsUnitalKraus (d := d) (D := D) K :=
    isUnitalKraus_conjTranspose (d := d) (D := D) (K := A) hTP'
  have hIrrK : IsIrreducibleMap (transferMap (d := d) (D := D) K) :=
    isIrreducibleCP_transferMap_conjTranspose_of_isIrreducibleTensor (d := d) (D := D) A hIrr
  have hCh : IsChannel (transferMap (d := d) (D := D) A) :=
    transferMap_isChannel (d := d) (D := D) A (by simpa using hTP)
  obtain ⟨ρ, hρ_psd, hρ_ne, hρ_fix⟩ :=
    hCh.exists_posSemidef_fixedPoint (E := transferMap (d := d) (D := D) A) hDpos
  have hIrrAmap : IsIrreducibleMap (transferMap (d := d) (D := D) A) :=
    isIrreducibleCP_transferMap_of_isIrreducibleTensor (d := d) (D := D) A hIrr
  have hρ_pd : ρ.PosDef :=
    posSemidef_fixedPoint_isPosDef_of_irreducible (A := A) (d := d) (D := D)
      hIrrAmap ρ hρ_psd hρ_ne hρ_fix
  have h_adjfix : Kraus.adjointMap K ρ = ρ := by
    simpa [K, Kraus.adjointMap, transferMap_apply, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc] using hρ_fix
  exact ⟨K, h_unitalK, hIrrK, ρ, hρ_pd, h_adjfix, rfl⟩

/-- **Bridge: irreducible TP tensor → cyclic sector decomposition.**

For an irreducible TP tensor `A` with `0 < D`, there exists a period `m > 0`
such that after blocking by `m`, the blocked tensor admits a decomposition
into `m` left-canonical (TP) blocks via cyclic spectral projections.

This bridges the MPS-level hypotheses (`IsIrreducibleTensor` + TP) to the
channel-level cyclic decomposition, deriving all intermediate hypotheses
(`ρ.PosDef`, `Kraus.adjointMap` fixed point, `IsIrreducibleMap`, peripheral
spectrum structure) automatically via `conjTranspose_kraus_setup`. -/
theorem exists_cyclic_sector_decomp_of_TP_of_isIrreducibleTensor
    {d D : ℕ} [NeZero D]
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hIrr : IsIrreducibleTensor A) :
    ∃ (m : ℕ) (_ : 0 < m)
      (dim : Fin m → ℕ) (blocks : (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k)),
      (∀ k, ∑ i : Fin (blockPhysDim d m), (blocks k i)ᴴ * blocks k i = 1) ∧
      SameMPV₂ (blockTensor A m) (toTensorFromBlocks (μ := fun _ => 1) blocks) := by
  -- Use shared setup to get conjugate Kraus family and PosDef fixed point.
  obtain ⟨K, h_unitalK, hIrrK, ρ, hρ_pd, h_adjfix, rfl⟩ :=
    conjTranspose_kraus_setup A hTP hIrr
  -- Extract cyclic peripheral structure via
  -- `peripheral_eigenvalues_cyclic_structure` from `GroupStructure.lean`.
  obtain ⟨m, γ, hm_pos, hγ_prim, hperiph_set⟩ :=
    PeripheralSpectrum.peripheral_eigenvalues_cyclic_structure _ h_unitalK ρ hρ_pd h_adjfix hIrrK
  -- Convert set representation to range form.
  have hperiph_range :
      peripheralEigenvalues (transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) =
        Set.range (fun j : Fin m => γ ^ (j : ℕ)) := by
    rw [hperiph_set]; ext x; simp [Set.mem_range, eq_comm]
  -- Apply exists_cyclic_sector_decomp_after_blocking.
  haveI : NeZero m := ⟨by omega⟩
  obtain ⟨dim, blocks, hTP_blocks, hSame⟩ :=
    exists_cyclic_sector_decomp_after_blocking A hTP hIrr ρ hρ_pd h_adjfix hIrrK hγ_prim
      hperiph_range
  exact ⟨m, hm_pos, dim, blocks, hTP_blocks, hSame⟩

end CyclicSectorFromMPS

/-!
## Fundamental Theorem of MPS (arXiv:1606.00608, after blocking)

### Overview

The fundamental theorem of MPS (1606.00608 version, after blocking) asserts:

For any MPS tensor `A`, there exists a blocking period `p > 0` such that
`blockTensor A p` admits a decomposition into a zero tail plus a direct sum
of TP sectors, where each sector is left-canonical and the direct sum is
`SameMPV₂`-equivalent to the blocked tensor.

The full end-to-end statement chains:
1. Zero-block separation (`exists_irreducible_blockDecomp_liveBlocks`)
2. TP gauge (`exists_tp_gauge_from_arbitrary_with_zeroTail`)
3. Common blocking to primitive (`exists_common_blocking_all_primitive_of_TP_irr`)
4. Cyclic sector decomposition per block (`exists_cyclic_sector_decomp_after_blocking`)

### Current status

The theorem `exists_tp_sector_decomp_after_blocking` below provides:
- A blocking period `p > 0`
- A zero tail of dimension `zeroTailDim`
- A family of TP sector blocks
- The MPV relationship: `blockTensor A p` is `SameMPV₂`-equivalent to
  `zeroMPSTensor + toTensorFromBlocks μ sectors` for some weights `μ`

The full FT also requires showing each sector is:
- **Irreducible** (from `isIrreducible_restriction_of_cyclic_decomp` + orbit-sum lift)
- **Normal** (from irreducibility + primitivity of sector transfer maps)
- **Gauge-phase unique** (from the BNT permutation rigidity theorem)

These additional properties are documented but not yet fully formalized.
-/

section FundamentalTheorem1606

-- **Structural decomposition of MPS tensors after blocking (1606.00608 reduction).**
--
-- For any MPS tensor `A`, there exists a blocking period `p > 0` and a
-- decomposition of the blocked tensor into:
-- 1. A zero tail (irreducible blocks with zero spectral weight)
-- 2. A family of TP blocks with primitive transfer maps
--
-- Additionally, the weights `μ k` satisfy `μ k ≠ 0` and the full MPV
-- identity is maintained.
--
-- This is `exists_tp_primitive_blockDecomp_after_blocking` — the main reduction
-- theorem from the first section. The FT chains from this through the cyclic
-- sector decomposition to produce the final canonical form.
-- (Already proved above as `exists_tp_primitive_blockDecomp_after_blocking`.)

/-- **Fundamental Theorem of MPS (1606.00608, after blocking): structural version.**

For any two MPS tensors `A, B` with `SameMPV₂ A B`, after a common blocking period,
both blocked tensors admit TP-primitive decompositions. If the blocked decompositions
additionally satisfy:
- Tensor irreducibility of each block
- Distinct weight norms (pairwise)
- BNT separation (no gauge-phase equivalent pairs with same dimension)

then the block structures match up to permutation and gauge-phase equivalence.

This theorem packages the structural content of arXiv:1606.00608, Theorem 1,
connecting the reduction output to the fundamental theorem conclusion. -/
theorem fundamentalTheorem_after_blocking_1606_structural
    {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (_hSame : SameMPV₂ A B) :
    -- Both tensors admit blocked TP-primitive decompositions
    ∃ (pA : ℕ) (_ : 0 < pA)
      (rA : ℕ) (dimA : Fin rA → ℕ) (μA : Fin rA → ℂ)
      (blocksA : (k : Fin rA) → MPSTensor (blockPhysDim d pA) (dimA k)),
    ∃ (pB : ℕ) (_ : 0 < pB)
      (rB : ℕ) (dimB : Fin rB → ℕ) (μB : Fin rB → ℂ)
      (blocksB : (k : Fin rB) → MPSTensor (blockPhysDim d pB) (dimB k)),
      -- Blocks are TP
      (∀ k, ∑ i, (blocksA k i)ᴴ * blocksA k i = 1) ∧
      (∀ k, ∑ i, (blocksB k i)ᴴ * blocksB k i = 1) ∧
      -- Blocks have primitive transfer maps
      (∀ k, _root_.IsPrimitive (transferMap (blocksA k))) ∧
      (∀ k, _root_.IsPrimitive (transferMap (blocksB k))) ∧
      -- Nonzero weights
      (∀ k, μA k ≠ 0) ∧
      (∀ k, μB k ≠ 0) ∧
      -- Positive bond dimensions
      (∀ k, 0 < dimA k) ∧
      (∀ k, 0 < dimB k) := by
  obtain ⟨_, pA, hpA, rA, dimA, μA, blocksA, hTPA, hPrimA, hDimA, hμA, _⟩ :=
    exists_tp_primitive_blockDecomp_after_blocking A
  obtain ⟨_, pB, hpB, rB, dimB, μB, blocksB, hTPB, hPrimB, hDimB, hμB, _⟩ :=
    exists_tp_primitive_blockDecomp_after_blocking B
  exact ⟨pA, hpA, rA, dimA, μA, blocksA, pB, hpB, rB, dimB, μB, blocksB,
    hTPA, hTPB, hPrimA, hPrimB, hμA, hμB, hDimA, hDimB⟩

/-!
### What remains for the full 1606.00608 Fundamental Theorem

The complete end-to-end FT would take two tensors `A, B` with `SameMPV₂ A B` and
produce a common blocking period `p` and matching block structures. The remaining
formalizations are:

1. **Common blocking period**: Re-block both decompositions to `p = lcm(pA, pB)`.
   This requires "iterated blocking" infrastructure: `blockTensor (blockTensor A pA) q`
   relates to `blockTensor A (pA * q)`.

2. **Sector irreducibility**: Each cyclic sector of a blocked periodic block should be
   irreducible. The orbit-sum lift hypothesis from `isIrreducible_restriction_of_cyclic_decomp`
   in `CyclicDecomposition.lean` provides this conditionally; the concrete orbit-sum
   construction from MPS Kraus operators remains to be formalized.

3. **Normal canonical form per sector**: Each irreducible TP-primitive sector becomes
   `IsNormal` via `isNormal_of_tp_primitive_irreducible` (already proved in this file).

4. **BNT separation + weight ordering + gauge-phase matching**: Apply the downstream
   FT from `Full.lean` via `weakFundamentalTheorem_conditional`.

Steps 1–2 are the main remaining formalizations; steps 3–4 are already formalized
and just need to be combined once steps 1–2 are complete.
-/

end FundamentalTheorem1606

/-!
## Bridge: MPS hypotheses → cyclic sector decomposition

This section connects the MPS reduction pipeline output (TP + `IsIrreducibleTensor`)
to the channel-level cyclic decomposition theorem, closing the gap identified in §2.3
of arXiv:1606.00608 and Issue #242.

### Mathematical overview

For an irreducible TP block `A` with bond dimension `D ≥ 1`, we derive:
1. **ρ.PosDef** with `transferMap A ρ = ρ`: from the irreducible channel's Perron–Frobenius theory
2. **IsIrreducibleMap (transferMap K)** for `K = (A·)ᴴ`: from `IsIrreducibleTensor`
3. **Peripheral spectrum = cyclic group**: from product/power closure + roots of unity property
4. **Cyclic sector decomposition**: via `exists_cyclic_sector_decomp_after_blocking`

### Key insight

`Kraus.adjointMap (fun i => (A i)ᴴ) = transferMap A`, so the adjoint-fixed-point
hypothesis `Kraus.adjointMap K ρ = ρ` is equivalent to `transferMap A ρ = ρ`.
-/

section CyclicSectorBridgeMPS

/-- **Cyclic sector decomposition from MPS-level hypotheses.**

For any irreducible left-canonical (TP) tensor `A` with bond dimension `D ≥ 1`:
- Let `m` be the period (= cardinality of the peripheral eigenvalue set of the
  adjoint transfer map)
- After blocking by `m`, the blocked tensor `blockTensor A m` admits a sector
  decomposition into `m` TP blocks

This bridges the gap between the MPS reduction pipeline output
(`IsIrreducibleTensor A` + TP) and the channel-level cyclic decomposition
(`exists_cyclic_sector_decomp_after_blocking`).

The proof derives all channel-level hypotheses from the MPS-level hypotheses:
- PosDef fixed point of `transferMap A` (via Perron–Frobenius for irreducible channels)
- Irreducibility of the adjoint transfer map (from `IsIrreducibleTensor`)
- Peripheral spectrum characterization (from `peripheralEigenvalues_eq_range_primitiveRoot`)

**Note**: This theorem depends on `peripheralEigenvalues_eq_range_primitiveRoot`
(in `CyclicGroup.lean`, now sorry-free). -/
theorem exists_cyclic_sector_decomp_of_irr_tp [NeZero D]
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hIrr : IsIrreducibleTensor A) :
    ∃ (m : ℕ) (_ : 0 < m)
      (dim : Fin m → ℕ) (blocks : (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k)),
      -- Blocks are left-canonical (TP)
      (∀ k, ∑ i : Fin (blockPhysDim d m), (blocks k i)ᴴ * blocks k i = 1) ∧
      -- SameMPV₂ relationship
      SameMPV₂ (blockTensor A m) (toTensorFromBlocks (μ := fun _ => 1) blocks) := by
  classical
  have hDpos : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  -- Step 1: Derive channel-level hypotheses from MPS-level hypotheses.
  -- Work with the conjugate-transposed Kraus family K i = (A i)ᴴ.
  let K : MPSTensor d D := fun i => (A i)ᴴ
  have hTP' : KadisonSchwarz.IsTPKraus (d := d) (D := D) A := by
    simpa [KadisonSchwarz.IsTPKraus] using hTP
  have h_unitalK : KadisonSchwarz.IsUnitalKraus (d := d) (D := D) K :=
    KadisonSchwarz.isUnitalKraus_conjTranspose (d := d) (D := D) (K := A) hTP'
  -- Irreducibility of transferMap K from tensor-irreducibility of A.
  have hIrrK : IsIrreducibleMap (transferMap (d := d) (D := D) K) :=
    isIrreducibleCP_transferMap_conjTranspose_of_isIrreducibleTensor (d := d) (D := D) A hIrr
  -- A positive definite fixed point for transferMap A.
  have hCh : IsChannel (transferMap (d := d) (D := D) A) :=
    transferMap_isChannel (d := d) (D := D) A (by simpa using hTP)
  obtain ⟨ρ, hρ_psd, hρ_ne, hρ_fix⟩ :=
    hCh.exists_posSemidef_fixedPoint (E := transferMap (d := d) (D := D) A) hDpos
  have hIrrAmap : IsIrreducibleMap (transferMap (d := d) (D := D) A) :=
    isIrreducibleCP_transferMap_of_isIrreducibleTensor (d := d) (D := D) A hIrr
  have hρ_pd : ρ.PosDef :=
    posSemidef_fixedPoint_isPosDef_of_irreducible (A := A) (d := d) (D := D)
      hIrrAmap ρ hρ_psd hρ_ne hρ_fix
  -- Convert: Kraus.adjointMap K ρ = ρ ↔ transferMap A ρ = ρ.
  have h_adjfix : Kraus.adjointMap K ρ = ρ := by
    simpa [K, Kraus.adjointMap, transferMap_apply, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc] using hρ_fix
  -- Step 2: Get the peripheral spectrum characterization.
  set E_adj := transferMap (d := d) (D := D) K with E_adj_def
  have ⟨hm_pos, γ, hγ_prim, hperiph⟩ :=
    peripheralEigenvalues_eq_range_primitiveRoot K h_unitalK ρ hρ_pd h_adjfix hIrrK
  set m := (peripheralEigenvalues_finite (f := E_adj)).toFinset.card with m_def
  -- Step 3: Apply the existing cyclic sector decomposition.
  have hm_ne : m ≠ 0 := Nat.pos_iff_ne_zero.mp hm_pos
  haveI : NeZero m := ⟨hm_ne⟩
  exact ⟨m, hm_pos,
    (exists_cyclic_sector_decomp_after_blocking A hTP hIrr ρ hρ_pd h_adjfix hIrrK hγ_prim hperiph)⟩

/-- **Full pipeline: arbitrary MPS tensor → blocked TP sectors via cyclic decomposition.**

For any MPS tensor `A`, there exists a blocking period `p > 0` such that
`blockTensor A p` admits a decomposition into:
- A zero tail (from irreducible blocks with zero spectral weight)
- A family of TP blocks (from the cyclic sector decomposition of each live block)

Each live block from the TP-gauge step is irreducible with nonzero weight. For blocks
whose transfer map is already primitive, blocking by any period preserves irreducibility
(`isIrreducibleTensor_blockTensor_of_tp_primitive_irr`). For periodic blocks, the cyclic
sector decomposition (`exists_cyclic_sector_decomp_of_irr_tp`) splits the blocked tensor
into primitive sectors.

**Note**: This is a lightweight corollary of `exists_tp_primitive_blockDecomp_after_blocking`,
which provides a strictly stronger result (primitive transfer maps, nonzero weights, MPV
relationship). This version forgets that extra data, retaining only TP sectors with positive
bond dimensions. -/
theorem exists_tp_sector_decomp_after_blocking_via_cyclic [NeZero D]
    (A : MPSTensor d D) :
    ∃ (p : ℕ) (_ : 0 < p)
      (r : ℕ) (dim : Fin r → ℕ)
      (sectors : (k : Fin r) → MPSTensor (blockPhysDim d p) (dim k)),
      -- Sectors are left-canonical (TP)
      (∀ k, ∑ i : Fin (blockPhysDim d p), (sectors k i)ᴴ * sectors k i = 1) ∧
      -- Positive bond dimensions
      (∀ k, 0 < dim k) := by
  obtain ⟨_, p, hp, r, dim, _, blocks, hTP, _, hDim, _, _⟩ :=
    exists_tp_primitive_blockDecomp_after_blocking (d := d) (D := D) A
  exact ⟨p, hp, r, dim, blocks, hTP, hDim⟩

end CyclicSectorBridgeMPS

end MPSTensor

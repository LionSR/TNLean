/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.NormalPipeline
import TNLean.MPS.Core.BlockingInfrastructure
import TNLean.MPS.FundamentalTheorem.Full
import TNLean.Wielandt.SpanGrowth.VectorToMatrixSpan
import TNLean.Wielandt.SpanGrowth.CumulativeSpan
import TNLean.Wielandt.RectangularSpan.Basic

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Filter

/-!
# End-to-end canonical form assembly (arXiv:1606.00608, §2.3 + Appendix A)

This file assembles the individual pipeline components into end-to-end theorems
connecting an **arbitrary MPS tensor** to a blocked canonical form.

## Pipeline overview

The assembly threads through the following components:

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

### Possible resolutions

1. **Cyclic sector decomposition** (paper §2.3): decompose each periodic block into
   primitive cyclic sectors. This is the mathematically correct approach (~800-1200 LOC).

2. **Direct route for the primitive case**: If a block happens to already be primitive
   (period 1), then `p = 1` suffices and `isIrreducibleTensor_blockTensor_one`
   from `NormalPipeline.lean` gives irreducibility directly. The
   `exists_normalCanonicalForm_of_primitive_blockDecomp` theorem handles this.

## References

- [Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608, §2.3 + Appendix A]
- [Cirac–Pérez-García–Schuch–Verstraete, arXiv:2011.12127, §IV]
-/

namespace MPSTensor

variable {d D : ℕ}

/-!
## The main assembly theorem

We compose the individual pipeline steps into a single theorem that takes
an arbitrary `A : MPSTensor d D` and produces blocked TP-primitive data.
-/

/-- **Main assembly: arbitrary MPS tensor → blocked TP-primitive decomposition.**

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
that the pipeline does not produce automatically (see gap documentation above).
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
## Pipeline shortcut for pre-primitive blocks

When the input already has primitive blocks with distinct weight norms
(e.g., from an external construction or a tensor that is already aperiodic),
the blocking step is trivial (p = 1) and the full `IsNormalCanonicalForm`
follows directly via `exists_normalCanonicalForm_of_primitive_blockDecomp`.
-/

/-- **Pipeline shortcut for pre-primitive blocks.**

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
   → `isPrimitive_of_peripheralPrimitive_of_irreducible` → `∃ ρ, IsPrimitiveMPS A ρ`
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
- Peripheral primitivity + irreducibility → spectral-gap primitivity
- Spectral-gap + irreducibility → PosDef fixed point
- Spectral-gap + PosDef → HasEventuallyFullKrausRank → IsNormal -/
theorem isNormal_of_tp_primitive_irreducible [NeZero D]
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : _root_.IsPrimitive (transferMap (d := d) (D := D) A))
    (hIrr : IsIrreducibleTensor A) :
    IsNormal A := by
  -- Step 1: Get spectral-gap primitivity from peripheral primitivity + irreducibility.
  have hMPSPrim : MPSTensor.IsPrimitive A :=
    isPrimitive_of_peripheralPrimitive_of_irreducible A hIrr hTP hPrim
  -- Step 2: Extract the PSD fixed point.
  obtain ⟨ρ, hPrimMPS⟩ := hMPSPrim
  -- Step 3: Upgrade PSD → PosDef using tensor irreducibility.
  have hPD : ρ.PosDef :=
    posDef_of_isIrreducibleTensor_of_isPrimitiveMPS hPrimMPS hIrr
  -- Step 4: IsNormal from spectral gap + PosDef.
  exact isNormal_of_isPrimitiveMPS_with_posDef hPrimMPS hPD

/-!
## Combined pipeline: arbitrary → IsNormal (per block, for primitive blocks)

For the pre-blocking blocks (which ARE irreducible), the chain to IsNormal
works directly. This shows that the original (unblocked) live blocks become
normal once we know their transfer maps are primitive.
-/

/-- **Pre-blocking blocks are normal once primitive.**

For the live blocks from the arbitrary-input TP gauge pipeline, if a block
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
## Weak FT: proportional MPVs → block matching (for TP-primitive blocks)

This packages the full pipeline output together with the downstream
FT theorems, showing how the assembly connects to the fundamental theorem
conclusions.

For two arbitrary tensors A, B with proportional MPVs, the pipeline produces
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

end MPSTensor

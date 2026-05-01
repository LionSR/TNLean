/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Core.BlockingTransfer
import TNLean.MPS.FundamentalTheorem.Multi
import TNLean.MPS.CanonicalForm.BlockingViaAdjoint

import Mathlib.Algebra.GCDMonoid.Finset

/-!
# Blocking infrastructure: SameMPV₂ compatibility, primitivity under multiples, common period

This file contains the **Tier 3** blocking infrastructure needed to go from
per-block periodicity removal to a common blocking period making all blocks
primitive simultaneously.

## Main results

### Part A: SameMPV₂ blocking
* `sameMPV₂_blockTensor_of_sameMPV₂_toTensorFromBlocks` — Blocking distributes over
  `toTensorFromBlocks`: if `SameMPV₂ A (toTensorFromBlocks μ blocks)`, then
  `SameMPV₂ (blockTensor A p) (toTensorFromBlocks (μ^p) (blockTensor blocks p))`.

### Part B: Primitivity under multiples
* `isPrimitive_pow_of_isPrimitive` — primitive channels remain primitive under positive powers.
* `isPrimitive_transferMap_blockTensor_of_dvd` — transfer-map primitivity is monotone
  in the blocking period (for multiples).

### Part C: Common period via LCM
* `lcmPeriod`, `lcmPeriod_pos`, `dvd_lcmPeriod` — lightweight LCM helpers on `Fin k → ℕ`
  families used throughout common-period blocking.
* `exists_common_blocking_all_primitive` — given a family of blocks each admitting some
  primitivity period, there exists a single common period.
* `exists_common_blocking_all_primitive_of_TP_irr` — convenience entry point from TP +
  irreducible hypotheses.

## References

* [arXiv:1606.00608, Appendix A — periodicity removal by blocking]
* [arXiv:2011.12127, §IV — canonical form construction]
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-!
## Part A: SameMPV₂ compatibility under blocking

The key observation: `blockTensor T p` computes `mpv` via flattened words,
and the flattening depends only on the blocked configuration `σ` and the
period `p`, not on the tensor `T`. This lets us "push blocking through"
`toTensorFromBlocks`.
-/

section SameMPV₂Blocking

variable {D : ℕ} {r : ℕ} {dim : Fin r → ℕ}

/-- Flatten a blocked configuration to the underlying word of original physical indices. -/
private noncomputable def blockedFlatWord (p : ℕ) {N : ℕ}
    (σ : Fin N → Fin (blockPhysDim d p)) : List (Fin d) :=
  flattenBlockedWord d p (List.ofFn σ)

/-- The flattened word of an `N`-site blocked configuration has length `N * p`. -/
private theorem length_blockedFlatWord (p : ℕ) {N : ℕ}
    (σ : Fin N → Fin (blockPhysDim d p)) :
    (blockedFlatWord (d := d) p σ).length = N * p := by
  simpa [blockedFlatWord] using
    (length_flattenBlockedWord (d := d) (L := p) (List.ofFn σ))

/-- The flattened configuration associated to a blocked physical configuration. -/
noncomputable def blockedFlatConfig (p : ℕ) {N : ℕ}
    (σ : Fin N → Fin (blockPhysDim d p)) : Fin (N * p) → Fin d :=
  fun i =>
    (blockedFlatWord (d := d) p σ).get
      (Fin.cast (length_blockedFlatWord (d := d) p σ).symm i)

/-- Reconstruct the flattened blocked word from `blockedFlatConfig`. -/
private theorem ofFn_blockedFlatConfig (p : ℕ) {N : ℕ}
    (σ : Fin N → Fin (blockPhysDim d p)) :
    List.ofFn (blockedFlatConfig (d := d) p σ) = blockedFlatWord (d := d) p σ := by
  unfold blockedFlatConfig
  conv_rhs => rw [← List.ofFn_get (blockedFlatWord (d := d) p σ)]
  have hcongr :=
    (List.ofFn_congr (m := N * p) (n := (blockedFlatWord (d := d) p σ).length)
      (length_blockedFlatWord (d := d) p σ).symm
      (fun i : Fin (N * p) =>
        (blockedFlatWord (d := d) p σ).get
          (Fin.cast (length_blockedFlatWord (d := d) p σ).symm i)))
  simpa [Function.comp, Fin.cast_cast] using hcongr

/-- Evaluating the blocked tensor on a blocked configuration agrees with evaluating
    the original tensor on the flattened configuration. -/
theorem mpv_blockTensor_eq_mpv_blockedFlatConfig
    {D' : ℕ} (T : MPSTensor d D') (p : ℕ) {N : ℕ}
    (σ : Fin N → Fin (blockPhysDim d p)) :
    mpv (blockTensor (d := d) (D := D') T p) σ =
      mpv T (blockedFlatConfig (d := d) p σ) := by
  simp [mpv, coeff, ofFn_blockedFlatConfig (d := d) p σ,
    blockedFlatWord, evalWord_blockTensor]

/-- Blocking distributes over `toTensorFromBlocks`: if
`SameMPV₂ A (toTensorFromBlocks μ blocks)`, then blocking by `p` on both sides gives
`SameMPV₂ (blockTensor A p) (toTensorFromBlocks (μ^p) (blockTensor blocks p))`.

The mathematical content is: `V_N(blockTensor A p) = V_{Np}(A)` after identifying
physical indices, and the block-diagonal expansion of `toTensorFromBlocks` respects
this identification with exponents scaling from `N * p` to `N` by `(μ^p)^N = μ^(Np)`. -/
theorem sameMPV₂_blockTensor_of_sameMPV₂_toTensorFromBlocks
    (A : MPSTensor d D)
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hSame : SameMPV₂ A (toTensorFromBlocks μ blocks))
    (p : ℕ) :
    SameMPV₂
      (blockTensor (d := d) (D := D) A p)
      (toTensorFromBlocks (d := blockPhysDim d p)
        (fun k => (μ k) ^ p) (fun k => blockTensor (d := d) (D := dim k) (blocks k) p)) := by
  intro N σ
  let σflat := blockedFlatConfig (d := d) p σ
  calc
    mpv (blockTensor (d := d) (D := D) A p) σ
        = mpv A σflat := mpv_blockTensor_eq_mpv_blockedFlatConfig (d := d) A p σ
    _ = mpv (toTensorFromBlocks μ blocks) σflat := hSame (N * p) σflat
    _ = ∑ k : Fin r, (μ k) ^ (N * p) • mpv (blocks k) σflat := by
          exact mpv_toTensorFromBlocks_eq_sum μ blocks σflat
    _ = ∑ k : Fin r,
          ((μ k) ^ p) ^ N • mpv (blockTensor (d := d) (D := dim k) (blocks k) p) σ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          have hpow : (μ k) ^ (N * p) = ((μ k) ^ p) ^ N := by
            rw [Nat.mul_comm, pow_mul]
          rw [hpow, (mpv_blockTensor_eq_mpv_blockedFlatConfig (d := d) (blocks k) p σ).symm]
    _ = mpv (toTensorFromBlocks (d := blockPhysDim d p)
          (fun k => (μ k) ^ p) (fun k => blockTensor (d := d) (D := dim k) (blocks k) p)) σ := by
          exact (mpv_toTensorFromBlocks_eq_sum
            (fun k => (μ k) ^ p)
            (fun k => blockTensor (d := d) (D := dim k) (blocks k) p) σ).symm

/-- Blocking preserves `SameMPV₂` directly. -/
theorem sameMPV₂_blockTensor
    {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B) (p : ℕ) :
    SameMPV₂
      (blockTensor (d := d) (D := D₁) A p)
      (blockTensor (d := d) (D := D₂) B p) := by
  intro N σ
  let σflat := blockedFlatConfig (d := d) p σ
  calc
    mpv (blockTensor (d := d) (D := D₁) A p) σ
        = mpv A σflat := mpv_blockTensor_eq_mpv_blockedFlatConfig (d := d) A p σ
    _ = mpv B σflat := hSame (N * p) σflat
    _ = mpv (blockTensor (d := d) (D := D₂) B p) σ :=
          (mpv_blockTensor_eq_mpv_blockedFlatConfig (d := d) B p σ).symm

/-- Blocking the assembled weighted block tensor is MPV-equivalent to assembling the
blocked blocks with powered weights. -/
theorem sameMPV₂_blockTensor_toTensorFromBlocks
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (p : ℕ) :
    SameMPV₂
      (blockTensor (d := d) (D := ∑ k : Fin r, dim k)
        (toTensorFromBlocks (d := d) (μ := μ) blocks) p)
      (toTensorFromBlocks (d := blockPhysDim d p)
        (fun k => (μ k) ^ p)
        (fun k => blockTensor (d := d) (D := dim k) (blocks k) p)) := by
  exact sameMPV₂_blockTensor_of_sameMPV₂_toTensorFromBlocks
    (d := d) (D := ∑ k : Fin r, dim k) (dim := dim)
    (A := toTensorFromBlocks (d := d) (μ := μ) blocks)
    μ blocks (by intro N σ; rfl) p

/-- Positive-length MPV equality is preserved by positive physical blocking. -/
theorem sameMPV₂Pos_blockTensor
    {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂Pos A B) (p : ℕ) (hp : 0 < p) :
    SameMPV₂Pos
      (blockTensor (d := d) (D := D₁) A p)
      (blockTensor (d := d) (D := D₂) B p) := by
  intro N hN σ
  let σflat := blockedFlatConfig (d := d) p σ
  calc
    mpv (blockTensor (d := d) (D := D₁) A p) σ
        = mpv A σflat := mpv_blockTensor_eq_mpv_blockedFlatConfig (d := d) A p σ
    _ = mpv B σflat := hSame (N * p) (Nat.mul_pos hN hp) σflat
    _ = mpv (blockTensor (d := d) (D := D₂) B p) σ :=
          (mpv_blockTensor_eq_mpv_blockedFlatConfig (d := d) B p σ).symm

/-- Positive-length equality of weighted nonzero-block tensors is preserved after
positive common blocking, with each weight transported to the corresponding power. -/
theorem sameMPV₂Pos_toTensorFromBlocks_blockPower
    {rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    (μA : Fin rA → ℂ) (blocksA : (k : Fin rA) → MPSTensor d (dimA k))
    (μB : Fin rB → ℂ) (blocksB : (k : Fin rB) → MPSTensor d (dimB k))
    (hSame : SameMPV₂Pos
      (toTensorFromBlocks (d := d) (μ := μA) blocksA)
      (toTensorFromBlocks (d := d) (μ := μB) blocksB))
    (p : ℕ) (hp : 0 < p) :
    SameMPV₂Pos
      (toTensorFromBlocks (d := blockPhysDim d p)
        (fun k => (μA k) ^ p)
        (fun k => blockTensor (d := d) (D := dimA k) (blocksA k) p))
      (toTensorFromBlocks (d := blockPhysDim d p)
        (fun k => (μB k) ^ p)
        (fun k => blockTensor (d := d) (D := dimB k) (blocksB k) p)) := by
  have hA := sameMPV₂_blockTensor_toTensorFromBlocks
    (d := d) (dim := dimA) μA blocksA p
  have hB := sameMPV₂_blockTensor_toTensorFromBlocks
    (d := d) (dim := dimB) μB blocksB p
  have hBlock : SameMPV₂Pos
      (blockTensor (d := d) (D := ∑ k : Fin rA, dimA k)
        (toTensorFromBlocks (d := d) (μ := μA) blocksA) p)
      (blockTensor (d := d) (D := ∑ k : Fin rB, dimB k)
        (toTensorFromBlocks (d := d) (μ := μB) blocksB) p) :=
    sameMPV₂Pos_blockTensor
      (d := d)
      (toTensorFromBlocks (d := d) (μ := μA) blocksA)
      (toTensorFromBlocks (d := d) (μ := μB) blocksB) hSame p hp
  intro N hN σ
  calc
    mpv (toTensorFromBlocks (d := blockPhysDim d p)
        (fun k => (μA k) ^ p)
        (fun k => blockTensor (d := d) (D := dimA k) (blocksA k) p)) σ
        = mpv (blockTensor (d := d) (D := ∑ k : Fin rA, dimA k)
            (toTensorFromBlocks (d := d) (μ := μA) blocksA) p) σ := (hA N σ).symm
    _ = mpv (blockTensor (d := d) (D := ∑ k : Fin rB, dimB k)
            (toTensorFromBlocks (d := d) (μ := μB) blocksB) p) σ := hBlock N hN σ
    _ = mpv (toTensorFromBlocks (d := blockPhysDim d p)
        (fun k => (μB k) ^ p)
        (fun k => blockTensor (d := d) (D := dimB k) (blocksB k) p)) σ := hB N σ

end SameMPV₂Blocking

/-! ## Weight transport under blocking and sector replication -/

section WeightTransport

variable {r : ℕ}

/-- Nonzero block weights remain nonzero after taking a blocking power. -/
theorem blockWeights_ne_zero
    (μ : Fin r → ℂ) (hμ : ∀ k, μ k ≠ 0) (p : ℕ) :
    ∀ k, (μ k) ^ p ≠ 0 := by
  intro k
  exact pow_ne_zero p (hμ k)

/-- Replicating a block weight over cyclic sectors preserves nonvanishing after
any family of blocking powers. -/
theorem replicatedWeights_pow_ne_zero
    {m : Fin r → ℕ}
    (μ : Fin r → ℂ) (hμ : ∀ k, μ k ≠ 0) (p : Fin r → ℕ) :
    ∀ x : Σ k : Fin r, Fin (m k), (μ x.1) ^ (p x.1) ≠ 0 := by
  intro x
  exact pow_ne_zero (p x.1) (hμ x.1)

/-- A nonzero sector phase can be multiplied into a transported block weight
without making the sector weight vanish. -/
theorem replicatedWeights_pow_mul_phase_ne_zero
    {m : Fin r → ℕ}
    (μ : Fin r → ℂ) (θ : (Σ k : Fin r, Fin (m k)) → ℂ)
    (hμ : ∀ k, μ k ≠ 0) (hθ : ∀ x, θ x ≠ 0) (p : Fin r → ℕ) :
    ∀ x : Σ k : Fin r, Fin (m k), (μ x.1) ^ (p x.1) * θ x ≠ 0 := by
  intro x
  exact mul_ne_zero (replicatedWeights_pow_ne_zero μ hμ p x) (hθ x)

end WeightTransport

/-!
## Physical-dimension casts and iterated blocking dimensions

These auxiliary lemmas keep the later common-blocking statements at a single physical
alphabet size.  Mathematically, they state that substituting equal physical
dimensions leaves the tensors and their MPV/transfer-map properties unchanged.
-/

/-- The physical dimension of an iterated blocking is the physical dimension of
direct blocking by the product length. -/
theorem blockPhysDim_blockPhysDim (d m n : ℕ) :
    blockPhysDim (blockPhysDim d m) n = blockPhysDim d (m * n) := by
  simp [blockPhysDim_eq_pow, pow_mul]

/-- Encode a word of length `L` as a single blocked physical index. -/
noncomputable def blockIndexOfList (d L : ℕ) (w : List (Fin d)) (h : w.length = L) :
    Fin (blockPhysDim d L) :=
  (Fintype.equivFin (Fin L → Fin d)) (fun i => w.get (Fin.cast h.symm i))

/-- Decoding the blocked index associated to a list returns the original list. -/
theorem wordOfBlock_blockIndexOfList (d L : ℕ) (w : List (Fin d))
    (h : w.length = L) :
    wordOfBlock d L (blockIndexOfList d L w h) = w := by
  classical
  unfold blockIndexOfList wordOfBlock decodeBlock
  conv_rhs => rw [← List.ofFn_get w]
  have hcongr :=
    (List.ofFn_congr (m := L) (n := w.length) h.symm
      (fun i : Fin L => w.get (Fin.cast h.symm i)))
  simpa [Function.comp, Fin.cast_cast, blockPhysDim] using hcongr

/-- The physical index of the direct block obtained from an iterated blocked index. -/
noncomputable def iteratedBlockIndex (d m n : ℕ)
    (i : Fin (blockPhysDim (blockPhysDim d m) n)) :
    Fin (blockPhysDim d (m * n)) :=
  let w := flattenBlockedWord d m (wordOfBlock (blockPhysDim d m) n i)
  have hw : w.length = m * n := by
    rw [length_flattenBlockedWord, length_wordOfBlock, Nat.mul_comm]
  blockIndexOfList d (m * n) w hw

/-- The directly blocked word associated to an iterated blocked index is the flattened word. -/
theorem wordOfBlock_iteratedBlockIndex (d m n : ℕ)
    (i : Fin (blockPhysDim (blockPhysDim d m) n)) :
    wordOfBlock d (m * n) (iteratedBlockIndex d m n i) =
      flattenBlockedWord d m (wordOfBlock (blockPhysDim d m) n i) := by
  classical
  unfold iteratedBlockIndex
  exact wordOfBlock_blockIndexOfList d (m * n)
    (flattenBlockedWord d m (wordOfBlock (blockPhysDim d m) n i)) _

/-- The position of the `t`-th letter in the `j`-th block of a word split into
`n` consecutive blocks of length `m`. -/
private theorem blockWordChunkIndex_lt (m n : ℕ) (j : Fin n) (t : Fin m) :
    m * (j : ℕ) + (t : ℕ) < m * n := by
  calc
    m * (j : ℕ) + (t : ℕ) < m * (j : ℕ) + m :=
      Nat.add_lt_add_left t.isLt _
    _ = m * ((j : ℕ) + 1) := by rw [Nat.mul_add, Nat.mul_one]
    _ ≤ m * n := Nat.mul_le_mul_left m (Nat.succ_le_of_lt j.isLt)

/-- The `j`-th length-`m` subword of a direct length-`m * n` blocked word. -/
noncomputable def blockWordChunk (d m n : ℕ) (i : Fin (blockPhysDim d (m * n)))
    (j : Fin n) : List (Fin d) :=
  List.ofFn fun t : Fin m =>
    decodeBlock d (m * n) i ⟨m * (j : ℕ) + (t : ℕ), blockWordChunkIndex_lt m n j t⟩

@[simp] theorem length_blockWordChunk (d m n : ℕ) (i : Fin (blockPhysDim d (m * n)))
    (j : Fin n) : (blockWordChunk d m n i j).length = m := by
  simp [blockWordChunk]

/-- Encode a direct length-`m * n` blocked index as an iterated blocked index by grouping
its decoded word into `n` consecutive blocks of length `m`. -/
noncomputable def directToIteratedBlockIndex (d m n : ℕ)
    (i : Fin (blockPhysDim d (m * n))) :
    Fin (blockPhysDim (blockPhysDim d m) n) :=
  blockIndexOfList (blockPhysDim d m) n
    (List.ofFn fun j : Fin n =>
      blockIndexOfList d m (blockWordChunk d m n i j) (length_blockWordChunk d m n i j))
    (by simp)

/-- Encoding the decoded word of a block gives back the original blocked index. -/
theorem blockIndexOfList_wordOfBlock (d L : ℕ) (i : Fin (blockPhysDim d L)) :
    blockIndexOfList d L (wordOfBlock d L i) (length_wordOfBlock d L i) = i := by
  classical
  unfold blockIndexOfList wordOfBlock decodeBlock
  simp [blockPhysDim]

/-- Decoding blocked physical indices as words is injective. -/
theorem wordOfBlock_injective (d L : ℕ) : Function.Injective (wordOfBlock d L) := by
  intro i j hij
  have hdecode : decodeBlock d L i = decodeBlock d L j := by
    exact List.ofFn_injective hij
  unfold decodeBlock at hdecode
  exact (Fintype.equivFin (Fin L → Fin d)).symm.injective hdecode

/-- Flattening the grouped iterated index recovers the direct blocked word. -/
theorem flattenBlockedWord_wordOfBlock_directToIteratedBlockIndex (d m n : ℕ)
    (i : Fin (blockPhysDim d (m * n))) :
    flattenBlockedWord d m
        (wordOfBlock (blockPhysDim d m) n (directToIteratedBlockIndex d m n i)) =
      wordOfBlock d (m * n) i := by
  classical
  unfold directToIteratedBlockIndex
  rw [wordOfBlock_blockIndexOfList]
  simp only [flattenBlockedWord, List.map_ofFn]
  change (List.ofFn (fun j : Fin n =>
    wordOfBlock d m (blockIndexOfList d m (blockWordChunk d m n i j) _))).flatten =
      wordOfBlock d (m * n) i
  simp_rw [wordOfBlock_blockIndexOfList]
  simpa [blockWordChunk, wordOfBlock] using
    (List.ofFn_mul' (m := m) (n := n) (f := decodeBlock d (m * n) i)).symm

/-- Direct blocking is recovered after grouping a direct blocked index and then flattening
it through the iterated-blocking map. -/
theorem wordOfBlock_iteratedBlockIndex_directToIteratedBlockIndex (d m n : ℕ)
    (i : Fin (blockPhysDim d (m * n))) :
    wordOfBlock d (m * n) (iteratedBlockIndex d m n (directToIteratedBlockIndex d m n i)) =
      wordOfBlock d (m * n) i := by
  rw [wordOfBlock_iteratedBlockIndex,
    flattenBlockedWord_wordOfBlock_directToIteratedBlockIndex]

/-- Grouping a direct blocked index and then flattening the iterated index recovers the
original direct blocked index. -/
theorem iteratedBlockIndex_directToIteratedBlockIndex (d m n : ℕ)
    (i : Fin (blockPhysDim d (m * n))) :
    iteratedBlockIndex d m n (directToIteratedBlockIndex d m n i) = i := by
  exact wordOfBlock_injective d (m * n)
    (wordOfBlock_iteratedBlockIndex_directToIteratedBlockIndex d m n i)

/-- The map grouping a direct blocked word into iterated blocked words is surjective. -/
theorem directToIteratedBlockIndex_surjective (d m n : ℕ) :
    Function.Surjective (directToIteratedBlockIndex d m n) := by
  have hLeft : Function.LeftInverse (iteratedBlockIndex d m n) (directToIteratedBlockIndex d m n) :=
    iteratedBlockIndex_directToIteratedBlockIndex d m n
  have hInjective : Function.Injective (directToIteratedBlockIndex d m n) := hLeft.injective
  have hEquiv : Fin (blockPhysDim d (m * n)) ≃
      Fin (blockPhysDim (blockPhysDim d m) n) :=
    finCongr (blockPhysDim_blockPhysDim d m n).symm
  exact (Finite.injective_iff_surjective_of_equiv hEquiv).mp hInjective

/-- Flattening an iterated blocked index and then grouping it back recovers the iterated
blocked index. -/
theorem directToIteratedBlockIndex_iteratedBlockIndex (d m n : ℕ)
    (i : Fin (blockPhysDim (blockPhysDim d m) n)) :
    directToIteratedBlockIndex d m n (iteratedBlockIndex d m n i) = i := by
  have hLeft : Function.LeftInverse (iteratedBlockIndex d m n) (directToIteratedBlockIndex d m n) :=
    iteratedBlockIndex_directToIteratedBlockIndex d m n
  exact hLeft.rightInverse_of_surjective (directToIteratedBlockIndex_surjective d m n) i

/-- The canonical bijection between direct length-`m * n` blocked indices and iterated
length-`n` blocked indices obtained by grouping consecutive length-`m` words. -/
noncomputable def directIteratedBlockEquiv (d m n : ℕ) :
    Fin (blockPhysDim d (m * n)) ≃ Fin (blockPhysDim (blockPhysDim d m) n) where
  toFun := directToIteratedBlockIndex d m n
  invFun := iteratedBlockIndex d m n
  left_inv := iteratedBlockIndex_directToIteratedBlockIndex d m n
  right_inv := directToIteratedBlockIndex_iteratedBlockIndex d m n

@[simp] theorem directIteratedBlockEquiv_apply (d m n : ℕ)
    (i : Fin (blockPhysDim d (m * n))) :
    directIteratedBlockEquiv d m n i = directToIteratedBlockIndex d m n i := rfl

@[simp] theorem directIteratedBlockEquiv_symm_apply (d m n : ℕ)
    (i : Fin (blockPhysDim (blockPhysDim d m) n)) :
    (directIteratedBlockEquiv d m n).symm i = iteratedBlockIndex d m n i := rfl

/-- A direct index is the grouping of a direct blocked word exactly when flattening it
recovers that direct blocked index. -/
theorem eq_directToIteratedBlockIndex_iff_iteratedBlockIndex_eq (d m n : ℕ)
    (i : Fin (blockPhysDim d (m * n)))
    (j : Fin (blockPhysDim (blockPhysDim d m) n)) :
    j = directToIteratedBlockIndex d m n i ↔ iteratedBlockIndex d m n j = i := by
  constructor
  · intro h
    rw [h, iteratedBlockIndex_directToIteratedBlockIndex]
  · intro h
    calc
      j = directToIteratedBlockIndex d m n (iteratedBlockIndex d m n j) :=
        (directToIteratedBlockIndex_iteratedBlockIndex d m n j).symm
      _ = directToIteratedBlockIndex d m n i := by
        rw [h]

/-- Rewriting the blocking length does not change the decoded blocked word. -/
theorem wordOfBlock_cast_length (d : ℕ) {L₁ L₂ : ℕ} (h : L₁ = L₂)
    (i : Fin (blockPhysDim d L₁)) :
    wordOfBlock d L₂ (Fin.cast (congr_arg (blockPhysDim d) h) i) = wordOfBlock d L₁ i := by
  subst h
  rfl

/-- Reindex the physical alphabet of a tensor by a map of physical indices. -/
noncomputable def reindexPhysical {d₁ d₂ D : ℕ} (f : Fin d₁ → Fin d₂)
    (A : MPSTensor d₂ D) : MPSTensor d₁ D :=
  fun i => A (f i)

/-- Iterated physical blocking agrees with direct blocking after the canonical
index relabeling from iterated blocks to flattened blocks. -/
theorem blockTensor_blockTensor_apply {D : ℕ} (A : MPSTensor d D) (m n : ℕ)
    (i : Fin (blockPhysDim (blockPhysDim d m) n)) :
    blockTensor (d := blockPhysDim d m) (D := D)
        (blockTensor (d := d) (D := D) A m) n i =
      blockTensor (d := d) (D := D) A (m * n) (iteratedBlockIndex d m n i) := by
  simp [blockTensor, evalWord_blockTensor, wordOfBlock_iteratedBlockIndex]

/-- Tensor form of iterated blocking versus direct blocking with physical relabeling. -/
theorem blockTensor_blockTensor_eq_reindex {D : ℕ} (A : MPSTensor d D) (m n : ℕ) :
    blockTensor (d := blockPhysDim d m) (D := D)
        (blockTensor (d := d) (D := D) A m) n =
      reindexPhysical (iteratedBlockIndex d m n)
        (blockTensor (d := d) (D := D) A (m * n)) := by
  funext i
  exact blockTensor_blockTensor_apply (d := d) A m n i

/-- Iterated physical blocking and direct blocking have the same MPV family after
the natural relabeling of physical indices. -/
theorem sameMPV₂_blockTensor_blockTensor_mul_reindex {D : ℕ}
    (A : MPSTensor d D) (m n : ℕ) :
    SameMPV₂
      (blockTensor (d := blockPhysDim d m) (D := D)
        (blockTensor (d := d) (D := D) A m) n)
      (reindexPhysical (iteratedBlockIndex d m n)
        (blockTensor (d := d) (D := D) A (m * n))) := by
  rw [blockTensor_blockTensor_eq_reindex]
  intro N σ
  rfl

/-- Casting the physical dimension of both tensors preserves heterogeneous MPV equality. -/
theorem sameMPV₂_cast_physDim {d₁ d₂ D₁ D₂ : ℕ} (h : d₁ = d₂)
    (A : MPSTensor d₁ D₁) (B : MPSTensor d₁ D₂) :
    SameMPV₂
        (cast (congr_arg (fun d' => MPSTensor d' D₁) h) A)
        (cast (congr_arg (fun d' => MPSTensor d' D₂) h) B) ↔
      SameMPV₂ A B := by
  subst h
  rfl

/-- Casting the physical dimension commutes with the block-diagonal tensor constructor. -/
theorem toTensorFromBlocks_cast_physDim {d₁ d₂ r : ℕ} {dim : Fin r → ℕ}
    (h : d₁ = d₂) (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d₁ (dim k)) :
    cast (congr_arg (fun d' => MPSTensor d' (∑ k : Fin r, dim k)) h)
        (toTensorFromBlocks (d := d₁) (μ := μ) blocks) =
      toTensorFromBlocks (d := d₂) (μ := μ)
        (fun k => cast (congr_arg (fun d' => MPSTensor d' (dim k)) h) (blocks k)) := by
  subst h
  rfl

/-- Evaluating a physical-dimension cast amounts to casting the physical index. -/
theorem cast_physDim_apply {d₁ d₂ D : ℕ} (h : d₁ = d₂)
    (A : MPSTensor d₁ D) (i : Fin d₂) :
    cast (congr_arg (fun d' => MPSTensor d' D) h) A i = A (Fin.cast h.symm i) := by
  subst h
  rfl

/-- Casting the physical dimension preserves trace-preserving normalization. -/
theorem leftCanonical_cast_physDim {d₁ d₂ D : ℕ} (h : d₁ = d₂)
    (A : MPSTensor d₁ D) :
    (∑ i : Fin d₂,
        (cast (congr_arg (fun d' => MPSTensor d' D) h) A i)ᴴ *
          cast (congr_arg (fun d' => MPSTensor d' D) h) A i = 1) ↔
      (∑ i : Fin d₁, (A i)ᴴ * A i = 1) := by
  subst h
  simp

/-- Casting the physical dimension preserves transfer-map primitivity. -/
theorem isPrimitive_transferMap_cast_physDim {d₁ d₂ D : ℕ} (h : d₁ = d₂)
    (A : MPSTensor d₁ D) :
    _root_.IsPrimitive
        (transferMap (d := d₂) (D := D)
          (cast (congr_arg (fun d' => MPSTensor d' D) h) A)) ↔
      _root_.IsPrimitive (transferMap (d := d₁) (D := D) A) := by
  subst h
  rfl

/-- Casting the physical dimension preserves tensor irreducibility. -/
theorem isIrreducibleTensor_cast_physDim {d₁ d₂ D : ℕ} (h : d₁ = d₂)
    (A : MPSTensor d₁ D) :
    IsIrreducibleTensor (cast (congr_arg (fun d' => MPSTensor d' D) h) A) ↔
      IsIrreducibleTensor A := by
  subst h
  rfl

/-!
## Part B: Primitivity under multiples

If the transfer map of `blockTensor A p` is primitive and `p ∣ q`, then the
transfer map of `blockTensor A q` is also primitive.

The mathematical content: peripheral eigenvalues of `E^m` are `{μ^m | μ ∈ periph(E)}`,
so if `periph(E) = {1}` then `periph(E^m) = {1}`.
-/

section PrimitivityMultiples

variable {D : ℕ}

/-- Primitive channels remain primitive under positive powers.

If `peripheralEigenvalues E = {1}` and `m > 0`, then `peripheralEigenvalues (E^m) = {1}`.
This follows because the only peripheral eigenvalue `1` satisfies `1^m = 1`, and
spectral mapping ensures no new peripheral eigenvalues arise. -/
theorem isPrimitive_pow_of_isPrimitive
    [NeZero D]
    (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (m : ℕ) (hm : 0 < m)
    (hPrim : _root_.IsPrimitive E) :
    _root_.IsPrimitive (E ^ m) := by
  -- Extract a nonzero fixed point from IsPrimitive.
  -- IsPrimitive says peripheralEigenvalues E = {1}, so 1 is an eigenvalue.
  have h1_mem : (1 : ℂ) ∈ peripheralEigenvalues E := by
    rw [hPrim]; exact rfl
  obtain ⟨ρ, hρ_ev⟩ := h1_mem.1.exists_hasEigenvector
  have hρ_ne : ρ ≠ 0 := (Module.End.hasEigenvector_iff.mp hρ_ev).2
  have hρ_fix : E ρ = ρ := by
    have := Module.End.mem_eigenspace_iff.mp (Module.End.hasEigenvector_iff.mp hρ_ev).1
    simpa using this
  -- All peripheral eigenvalues of E are 1, so μ^m = 1 for any peripheral eigenvalue μ.
  have hper : ∀ μ : ℂ, μ ∈ peripheralEigenvalues E → μ ^ m = 1 := by
    intro μ hμ
    have hμ1 : μ = 1 := by rw [hPrim] at hμ; exact hμ
    simp [hμ1]
  -- Apply the existing periodicity removal theorem.
  exact peripheralEigenvalues_pow_eq_singleton E hm hper ρ hρ_fix hρ_ne

/-- Transfer-map primitivity is monotone in the blocking period (for multiples).

If `blockTensor A p` has a primitive transfer map and `p ∣ q` with `q > 0`, then
`blockTensor A q` also has a primitive transfer map. The proof uses `transferMap_blockTensor`
to convert between blocking levels. -/
theorem isPrimitive_transferMap_blockTensor_of_dvd
    [NeZero D]
    (A : MPSTensor d D) (p q : ℕ) (hpq : p ∣ q) (hq : 0 < q)
    (hPrim : _root_.IsPrimitive
      (transferMap (d := blockPhysDim d p) (D := D) (blockTensor (d := d) (D := D) A p))) :
    _root_.IsPrimitive
      (transferMap (d := blockPhysDim d q) (D := D) (blockTensor (d := d) (D := D) A q)) := by
  obtain ⟨m, rfl⟩ := hpq
  -- p > 0 since p * m > 0
  have hp : 0 < p := by
    by_contra h; push Not at h; interval_cases p; simp at hq
  -- m > 0 since p * m > 0 and p > 0
  have hm : 0 < m := Nat.pos_of_mul_pos_left hq
  -- Rewrite transfer maps as iterates of the original transfer map.
  rw [transferMap_blockTensor]          -- goal: IsPrimitive ((transferMap A) ^ (p * m))
  rw [pow_mul]                          -- goal: IsPrimitive (((transferMap A) ^ p) ^ m)
  rw [← transferMap_blockTensor]        -- goal: IsPrimitive ((transferMap (blockTensor A p)) ^ m)
  exact isPrimitive_pow_of_isPrimitive _ m hm hPrim

end PrimitivityMultiples

/-!
## Part C: Common blocking period via LCM

Given a finite family of blocks, each admitting some blocking period that
makes its transfer map primitive, there exists a single common period
making all of them primitive simultaneously. The period is the LCM of
the individual periods.
-/

section CommonPeriod

/-- LCM of a finite family of periods indexed by `Fin k`. -/
noncomputable def lcmPeriod {k : ℕ} (periods : Fin k → ℕ) : ℕ :=
  Finset.univ.lcm periods

/-- The LCM of a positive family of periods is positive. -/
theorem lcmPeriod_pos {k : ℕ} {periods : Fin k → ℕ} (h : ∀ i, 0 < periods i) :
    0 < lcmPeriod periods := by
  refine Nat.pos_of_ne_zero ?_
  refine Finset.lcm_ne_zero_iff.2 ?_
  intro i _
  exact Nat.ne_of_gt (h i)

/-- Each member of the family divides the LCM of the family. -/
theorem dvd_lcmPeriod {k : ℕ} (periods : Fin k → ℕ) (i : Fin k) :
    periods i ∣ lcmPeriod periods :=
  Finset.dvd_lcm (Finset.mem_univ i)

/-- There exists a common blocking period making all block transfer maps primitive.

Given a family of blocks indexed by `Fin r`, where each block `k` has some period `p_k`
making `transferMap (blockTensor (blocks k) p_k)` primitive, the LCM of all `p_k`
serves as a universal period. -/
theorem exists_common_blocking_all_primitive
    {r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hDim : ∀ k, 0 < dim k)
    (hPer : ∀ k, ∃ p, 0 < p ∧
      _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := dim k)
          (blockTensor (d := d) (D := dim k) (blocks k) p))) :
    ∃ p, 0 < p ∧ ∀ k,
      _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := dim k)
          (blockTensor (d := d) (D := dim k) (blocks k) p)) := by
  classical
  -- Choose a period for each block.
  let pk : Fin r → ℕ := fun k => (hPer k).choose
  have pk_pos : ∀ k, 0 < pk k := fun k => (hPer k).choose_spec.1
  have pk_prim : ∀ k, _root_.IsPrimitive
      (transferMap (d := blockPhysDim d (pk k)) (D := dim k)
        (blockTensor (d := d) (D := dim k) (blocks k) (pk k))) :=
    fun k => (hPer k).choose_spec.2
  -- Take the LCM of all periods.
  let P := lcmPeriod pk
  have hP_pos : 0 < P := lcmPeriod_pos pk_pos
  refine ⟨P, hP_pos, fun k => ?_⟩
  have hk_dvd : pk k ∣ P := dvd_lcmPeriod pk k
  haveI : NeZero (dim k) := ⟨Nat.ne_of_gt (hDim k)⟩
  exact isPrimitive_transferMap_blockTensor_of_dvd (blocks k) (pk k) P hk_dvd hP_pos (pk_prim k)

/-- Common blocking from TP + irreducible hypotheses (the standard reduction entry point).

This combines `exists_blockTensor_isPrimitive_of_TP_of_isIrreducibleTensor` (per-block
periodicity removal) with `exists_common_blocking_all_primitive` (LCM common period). -/
theorem exists_common_blocking_all_primitive_of_TP_irr
    {r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hTP : ∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1)
    (hIrr : ∀ k, IsIrreducibleTensor (blocks k))
    (hDim : ∀ k, 0 < dim k) :
    ∃ p, 0 < p ∧ ∀ k,
      _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := dim k)
          (blockTensor (d := d) (D := dim k) (blocks k) p)) := by
  have hPer : ∀ k, ∃ p, 0 < p ∧
      _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := dim k)
          (blockTensor (d := d) (D := dim k) (blocks k) p)) := by
    intro k
    haveI : NeZero (dim k) := ⟨Nat.ne_of_gt (hDim k)⟩
    exact exists_blockTensor_isPrimitive_of_TP_of_isIrreducibleTensor
      (blocks k) (hTP k) (hIrr k) (hDim k)
  exact exists_common_blocking_all_primitive blocks hDim hPer

end CommonPeriod

end MPSTensor

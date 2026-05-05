/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.Assembly.TPPrimitiveReduction
import TNLean.MPS.Chain.BlockedChainFT

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Filter

/-!
# Normality consequences of TP-primitive irreducible blocks

This file collects the part of the canonical-form reduction that upgrades
TP-primitive irreducible blocks to normal blocks and shows that normality is
preserved by blocking.

The core chain is the standard Perron–Frobenius route: peripheral primitivity
and tensor irreducibility give a primitive fixed point, irreducibility upgrades
that fixed point to positive definiteness, and the positive-definite fixed point
implies normality. A separate word-span argument then shows that blocking keeps
normality.

## Main statements

* `isNormal_of_tp_primitive_irreducible` — TP, primitive transfer map, and
  tensor irreducibility imply normality.
* `exists_blockTensor_isInjective_of_tp_primitive_irreducible` — the same
  hypotheses give an extra blocking whose blocked tensor is one-site injective.
* `isNormal_live_block_of_primitive` — the same conclusion for a single
  nonzero-weight block from the reduction data.
* `isNormal_blockTensor_of_isNormal` — blocking preserves normality.

## References

* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608, Section 2.3 + Appendix A]
* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:2011.12127, Section IV]

## Tags

matrix product states, canonical form, normality, blocking
-/

namespace MPSTensor

variable {d D : ℕ}

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

We state this chain as a single theorem.
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

/-- **TP + primitive + irreducible → injective after blocking**.

Normality is eventual block injectivity.  Combining
`isNormal_of_tp_primitive_irreducible` with the equivalence between `N`-block
injectivity and one-site injectivity of `blockTensor A N` gives a blocking length
whose blocked tensor is injective. -/
theorem exists_blockTensor_isInjective_of_tp_primitive_irreducible [NeZero D]
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : _root_.IsPrimitive (transferMap (d := d) (D := D) A))
    (hIrr : IsIrreducibleTensor A) :
    ∃ L : ℕ, IsInjective (blockTensor A L) := by
  obtain ⟨L, hL⟩ := isNormal_of_tp_primitive_irreducible A hTP hPrim hIrr
  exact ⟨L, (isNBlkInjective_iff_blockTensor_isInjective A L).1 hL⟩

/-- A trace-preserving scalar tensor has a nonzero Kraus matrix. -/
private theorem exists_nonzero_kraus_of_tp [NeZero D]
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1) :
    ∃ i : Fin d, A i ≠ 0 := by
  by_contra hnone
  push Not at hnone
  have hsum_zero :
      ∑ i : Fin d, (A i)ᴴ * A i = (0 : Matrix (Fin D) (Fin D) ℂ) := by
    apply Finset.sum_eq_zero
    intro i _
    simp [hnone i]
  have hone_zero : (1 : Matrix (Fin D) (Fin D) ℂ) =
      (0 : Matrix (Fin D) (Fin D) ℂ) := by
    rw [← hTP, hsum_zero]
  let a : Fin D := ⟨0, NeZero.pos D⟩
  have hentry : (1 : Matrix (Fin D) (Fin D) ℂ) a a = 0 := by
    simpa using congr_fun (congr_fun hone_zero a) a
  exact one_ne_zero hentry

/-- A nonzero scalar matrix spans the scalar matrix algebra. -/
private theorem isInjective_of_dim_one_of_exists_nonzero
    (A : MPSTensor d 1) (hA : ∃ i : Fin d, A i ≠ 0) :
    IsInjective A := by
  obtain ⟨i₀, hi₀⟩ := hA
  rw [IsInjective]
  have hentry : A i₀ 0 0 ≠ 0 := by
    intro h
    apply hi₀
    ext i j
    have hi : i = 0 := Fin.eq_zero i
    have hj : j = 0 := Fin.eq_zero j
    subst hi
    subst hj
    simpa using h
  have hsingle :
      (ℂ ∙ A i₀ : Submodule ℂ (Matrix (Fin 1) (Fin 1) ℂ)) = ⊤ := by
    refine (Submodule.span_singleton_eq_top_iff ℂ (A i₀)).2 ?_
    intro M
    refine ⟨M 0 0 / A i₀ 0 0, ?_⟩
    ext i j
    have hi : i = 0 := Fin.eq_zero i
    have hj : j = 0 := Fin.eq_zero j
    subst hi
    subst hj
    simp [div_eq_mul_inv, hentry]
  exact eq_top_iff.mpr <| by
    rw [← hsingle]
    exact Submodule.span_mono (Set.singleton_subset_iff.mpr (Set.mem_range_self i₀))

/-- Zero-length word products cannot span a matrix algebra of dimension at least two. -/
private theorem wordSpan_zero_ne_top_of_two_le [NeZero D]
    (A : MPSTensor d D) (hD : 2 ≤ D) :
    wordSpan A 0 ≠ (⊤ : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ)) := by
  intro h
  have h1 : Module.finrank ℂ (wordSpan A 0) = 1 := by
    rw [wordSpan_zero, finrank_span_singleton one_ne_zero]
  rw [h, finrank_top] at h1
  simp only [Module.finrank_matrix, Fintype.card_fin,
    Module.finrank_self, mul_one] at h1
  have hfour : 2 * 2 ≤ D * D := Nat.mul_le_mul hD hD
  omega

/-- **TP + primitive + irreducible → injective after positive blocking**.

The normality witness may be zero in scalar bond dimension, so the positivity
claim is proved separately: scalar trace-preserving tensors are already
one-site injective, while dimensions at least two cannot have full
zero-length word span. -/
theorem exists_pos_blockTensor_isInjective_of_tp_primitive_irreducible [NeZero D]
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : _root_.IsPrimitive (transferMap (d := d) (D := D) A))
    (hIrr : IsIrreducibleTensor A) :
    ∃ L : ℕ, 0 < L ∧ IsInjective (blockTensor A L) := by
  by_cases hD : D = 1
  · subst D
    have hInj : IsInjective A :=
      isInjective_of_dim_one_of_exists_nonzero A (exists_nonzero_kraus_of_tp A hTP)
    exact ⟨1, Nat.zero_lt_one,
      (isNBlkInjective_iff_blockTensor_isInjective A 1).1
        (isNBlkInjective_one_of_isInjective hInj)⟩
  · have hD_pos : 0 < D := NeZero.pos D
    have hD_ge : 2 ≤ D := by omega
    obtain ⟨L, hL⟩ :=
      exists_blockTensor_isInjective_of_tp_primitive_irreducible A hTP hPrim hIrr
    refine ⟨L, ?_, hL⟩
    by_contra hL_nonpos
    have hL_zero : L = 0 := Nat.eq_zero_of_not_pos hL_nonpos
    subst L
    have hzero :
        wordSpan A 0 = (⊤ : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ)) :=
      (wordSpan_eq_top_iff_isNBlkInjective A 0).mpr
        ((isNBlkInjective_iff_blockTensor_isInjective A 0).2 hL)
    exact wordSpan_zero_ne_top_of_two_le A hD_ge hzero

/-!
## Combined reduction: arbitrary → IsNormal (per block, for primitive blocks)

For the pre-blocking blocks (which ARE irreducible), the chain to IsNormal
works directly. This shows that the original nonzero-weight blocks become
normal once we know their transfer maps are primitive.
-/

/-- **Pre-blocking blocks are normal once primitive.**

For the nonzero-weight blocks from the arbitrary-tensor TP-gauge reduction, if a
block additionally has a primitive transfer map, then it is normal. -/
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

/-- Fixed-length injectivity persists at positive multiples of the length. -/
theorem isNBlkInjective_mul_of_isNBlkInjective
    (A : MPSTensor d D) {N m : ℕ} (hm : 0 < m) (hN : IsNBlkInjective A N) :
    IsNBlkInjective A (m * N) := by
  have hwordN : wordSpan A N = ⊤ :=
    (wordSpan_eq_top_iff_isNBlkInjective A N).mpr hN
  exact (wordSpan_eq_top_iff_isNBlkInjective A (m * N)).mp
    (wordSpan_mul_eq_top_of_wordSpan_eq_top A hwordN m hm)

/-- One-site injectivity of a blocked tensor persists after a positive further
blocking, read back as direct blocking of the original tensor. -/
theorem blockTensor_isInjective_mul_of_blockTensor_isInjective
    (A : MPSTensor d D) {N m : ℕ} (hm : 0 < m)
    (hN : IsInjective (blockTensor A N)) :
    IsInjective (blockTensor A (m * N)) := by
  exact (isNBlkInjective_iff_blockTensor_isInjective A (m * N)).1
    (isNBlkInjective_mul_of_isNBlkInjective A hm
      ((isNBlkInjective_iff_blockTensor_isInjective A N).2 hN))

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


end MPSTensor

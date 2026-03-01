/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TNLean.Wielandt.CumulativeSpan
import TNLean.Wielandt.Lemma2b
import TNLean.Wielandt.RankOneProducts
import TNLean.Algebra.BurnsideMatrix
import TNLean.Algebra.BurnsideTheorem
import TNLean.Algebra.IrreducibleTensorAction

/-!
# From Cumulative Span to Word Span

This file proves that **cumulative span = ⊤** implies **word span = ⊤** under
an aperiodicity condition, closing the gap between `cumulativeSpan A N = ⊤`
(guaranteed by Burnside's theorem for irreducible tensors) and `IsNormal A`
(needed for the quantum Wielandt bound).

## Key insight: aperiodicity via `1 ∈ wordSpan A 1`

**Without aperiodicity, the implication is false.** Counterexample: `A₁ = e₁₂`,
`A₂ = e₂₁` generates `M₂(ℂ)` as an algebra (`algSpan = ⊤`), but `wordSpan A n`
alternates between `span{e₁₁, e₂₂}` (even n ≥ 2) and `span{e₁₂, e₂₁}` (odd n),
so no single level reaches `⊤`. The **period** of this tensor is 2.

The aperiodicity condition `1 ∈ wordSpan A 1` (the identity matrix lies in the
span of the Kraus operators) ensures that word spans are **monotone**:
`wordSpan A n ≤ wordSpan A (n+1)`. Once monotone, the cumulative span collapses
to the word span at the top level, yielding `wordSpan A N = ⊤`.

## Main results

* `exists_nonzero_trace_word_of_cumulativeSpan_eq_top`:
  From `cumulativeSpan A N = ⊤` and `NeZero D`, extract a word with nonzero trace.

* `wordSpan_mono_of_one_mem_wordSpan`:
  If `1 ∈ wordSpan A L`, then `wordSpan A n ≤ wordSpan A (n + L)`.

* `cumulativeSpan_eq_wordSpan_of_one_mem_wordSpan_one`:
  If `1 ∈ wordSpan A 1`, then `cumulativeSpan A n = wordSpan A n`.

* `isNormal_of_cumulativeSpan_eq_top_of_aperiodic`:
  If `cumulativeSpan A N = ⊤` and `1 ∈ wordSpan A 1`, then `IsNormal A`.

* `isNormal_of_algSpan_eq_top_of_aperiodic`:
  If `algSpan A = ⊤` and `1 ∈ wordSpan A 1`, then `IsNormal A`.

* `isNormal_of_isIrreducibleAction_of_aperiodic`:
  If `IsIrreducibleAction A`, `1 ∈ wordSpan A 1`, and `NeZero D`, then `IsNormal A`.

* `isNormal_of_isIrreducibleTensor_of_aperiodic`:
  If `IsIrreducibleTensor A`, `1 ∈ wordSpan A 1`, and `NeZero D`, then `IsNormal A`.

## References

* arXiv:0909.5347, Proposition 3
* arXiv:1606.00608, §2.3 (canonical form + periodicity discussion)
-/

open scoped Matrix
open MPSTensor

namespace MPSTensor

variable {d D : ℕ}

/-! ## Part 1: Nonzero-trace word extraction from cumulative span -/

/-- If `cumulativeSpan A N = ⊤` and `NeZero D`, there exists a word of length ≤ N
with nonzero trace.

**Proof**: `I ∈ cumulativeSpan A N = ⊤`, and `tr(I) = D ≠ 0`. Since trace is
linear and `I` is a combination of word evaluations of length ≤ N, at least one
such evaluation must have nonzero trace. -/
theorem exists_nonzero_trace_word_of_cumulativeSpan_eq_top [NeZero D]
    (A : MPSTensor d D) {N : ℕ} (hcs : cumulativeSpan A N = ⊤) :
    ∃ (w : List (Fin d)), w.length ≤ N ∧ Matrix.trace (evalWord A w) ≠ 0 := by
  by_contra hall
  push_neg at hall
  -- Set up the trace linear map.
  set trMap : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] ℂ := Matrix.traceLinearMap (Fin D) ℂ ℂ
  -- All generators of cumulativeSpan have zero trace → the whole span is in ker(tr).
  have hker : cumulativeSpan A N ≤ LinearMap.ker trMap := by
    apply Submodule.span_le.mpr
    rintro M ⟨w, hw, rfl⟩
    exact LinearMap.mem_ker.mpr (hall w hw)
  -- Extract: every element of cumulativeSpan has zero trace.
  have hzero : ∀ M ∈ cumulativeSpan A N, M.trace = 0 :=
    fun M hM => LinearMap.mem_ker.mp (hker hM)
  -- But I ∈ cumulativeSpan A N = ⊤ and tr(I) = D ≠ 0.
  have hI : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ cumulativeSpan A N :=
    hcs ▸ Submodule.mem_top
  have htrI : (1 : Matrix (Fin D) (Fin D) ℂ).trace ≠ 0 := by
    simp only [Matrix.trace_one, Fintype.card_fin, ne_eq, Nat.cast_eq_zero]
    exact_mod_cast NeZero.ne D
  exact htrI (hzero 1 hI)

/-! ## Part 2: Monotonicity from identity in word span -/

/-- If `1 ∈ wordSpan A L`, then `wordSpan A n ≤ wordSpan A (n + L)`.

**Proof**: For any `M ∈ wordSpan A n`, `M = M * 1 ∈ wordSpan A n * wordSpan A L ≤
wordSpan A (n + L)` by `wordSpan_mul_le`. -/
theorem wordSpan_mono_of_one_mem_wordSpan
    (A : MPSTensor d D) {L : ℕ}
    (hone : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ wordSpan A L) :
    ∀ n, wordSpan A n ≤ wordSpan A (n + L) := by
  intro n M hM
  have hmul : M * 1 ∈ wordSpan A n * wordSpan A L :=
    Submodule.mul_mem_mul hM hone
  rw [Matrix.mul_one] at hmul
  exact wordSpan_mul_le A n L hmul

/-- Monotonicity with step 1: if `1 ∈ wordSpan A 1`, then
`wordSpan A n ≤ wordSpan A (n + 1)`. -/
theorem wordSpan_mono_succ_of_one_mem_wordSpan_one
    (A : MPSTensor d D)
    (hone : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ wordSpan A 1) :
    ∀ n, wordSpan A n ≤ wordSpan A (n + 1) :=
  wordSpan_mono_of_one_mem_wordSpan A hone

/-- Generalized monotonicity: if `1 ∈ wordSpan A 1` and `n ≤ m`,
then `wordSpan A n ≤ wordSpan A m`. -/
theorem wordSpan_mono'_of_one_mem_wordSpan_one
    (A : MPSTensor d D)
    (hone : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ wordSpan A 1)
    {n m : ℕ} (hnm : n ≤ m) :
    wordSpan A n ≤ wordSpan A m := by
  -- Write m = n + k and induct on k via an auxiliary lemma.
  suffices h : ∀ k, wordSpan A n ≤ wordSpan A (n + k) by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm; exact h k
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    calc wordSpan A n ≤ wordSpan A (n + k) := ih
      _ ≤ wordSpan A (n + k + 1) :=
          wordSpan_mono_succ_of_one_mem_wordSpan_one A hone _
      _ = wordSpan A (n + (k + 1)) := by ring_nf

/-! ## Part 3: Cumulative span equals word span under monotonicity -/

/-- If `1 ∈ wordSpan A 1`, then `cumulativeSpan A n = wordSpan A n`.

**Proof**: The word span is monotone (from Part 2), so the supremum of
`wordSpan A 0, ..., wordSpan A n` equals `wordSpan A n` (the largest term).
Since `cumulativeSpan A n` is exactly this supremum, the result follows. -/
theorem cumulativeSpan_eq_wordSpan_of_one_mem_wordSpan_one
    (A : MPSTensor d D)
    (hone : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ wordSpan A 1) :
    ∀ n, cumulativeSpan A n = wordSpan A n := by
  intro n
  apply le_antisymm
  · -- ≤: each wordSpan A m (m ≤ n) is ≤ wordSpan A n by monotonicity.
    apply Submodule.span_le.mpr
    rintro M ⟨w, hw, rfl⟩
    exact wordSpan_mono'_of_one_mem_wordSpan_one A hone hw
      (evalWord_mem_wordSpan A w)
  · -- ≥: wordSpan A n ≤ cumulativeSpan A n always holds.
    exact wordSpan_le_cumulativeSpan A (le_refl n)

/-! ## Part 4: Main theorems -/

/-- **Main theorem**: if `cumulativeSpan A N = ⊤` and `1 ∈ wordSpan A 1`
(aperiodicity), then `IsNormal A`.

**Proof**: By monotonicity of word spans (from `1 ∈ wordSpan A 1`),
`cumulativeSpan A N = wordSpan A N`. So `wordSpan A N = ⊤`, giving
`IsNBlkInjective A N`, hence `IsNormal A`. -/
theorem isNormal_of_cumulativeSpan_eq_top_of_aperiodic
    (A : MPSTensor d D) {N : ℕ}
    (hcs : cumulativeSpan A N = ⊤)
    (hone : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ wordSpan A 1) :
    IsNormal A := by
  refine ⟨N, ?_⟩
  rw [← wordSpan_eq_top_iff_isNBlkInjective]
  rwa [← cumulativeSpan_eq_wordSpan_of_one_mem_wordSpan_one A hone]

/-- If `algSpan A = ⊤` and `1 ∈ wordSpan A 1` (aperiodicity), then `IsNormal A`.

Combines the Noetherian chain stabilization for the algebra span with the
aperiodicity condition. -/
theorem isNormal_of_algSpan_eq_top_of_aperiodic
    (A : MPSTensor d D)
    (halg : algSpan A = ⊤)
    (hone : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ wordSpan A 1) :
    IsNormal A := by
  obtain ⟨N, hN⟩ := exists_cumulativeSpan_eq_top_of_algSpan_eq_top A halg
  exact isNormal_of_cumulativeSpan_eq_top_of_aperiodic A hN hone

/-- If `IsIrreducibleAction A`, `1 ∈ wordSpan A 1`, and `NeZero D`, then `IsNormal A`.

The full chain:
```
IsIrreducibleAction A
  →  algSpan A = ⊤           (Burnside's theorem)
  →  ∃ N, cumulativeSpan = ⊤  (Noetherian chain stabilization)
  →  wordSpan A N = ⊤         (aperiodicity: 1 ∈ wordSpan A 1)
  =  IsNormal A
``` -/
theorem isNormal_of_isIrreducibleAction_of_aperiodic [NeZero D]
    (A : MPSTensor d D)
    (hIrr : IsIrreducibleAction A)
    (hone : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ wordSpan A 1) :
    IsNormal A := by
  exact isNormal_of_algSpan_eq_top_of_aperiodic A (burnside_matrix A hIrr) hone

/-- If `IsIrreducibleTensor A`, `1 ∈ wordSpan A 1`, and `NeZero D`, then `IsNormal A`.

Extends the chain with `IsIrreducibleTensor → IsIrreducibleAction`
(proved in `IrreducibleTensorAction.lean`). -/
theorem isNormal_of_isIrreducibleTensor_of_aperiodic [NeZero D]
    (A : MPSTensor d D)
    (hIrr : IsIrreducibleTensor A)
    (hone : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ wordSpan A 1) :
    IsNormal A :=
  isNormal_of_isIrreducibleAction_of_aperiodic A
    (isIrreducibleAction_of_isIrreducibleTensor A hIrr) hone

/-! ## Part 5: Additional useful lemmas -/

/-- The nonzero-trace word extraction gives an eigenvector with nonzero eigenvalue. -/
theorem exists_eigenvector_of_cumulativeSpan_eq_top [NeZero D]
    (A : MPSTensor d D) {N : ℕ} (hcs : cumulativeSpan A N = ⊤) :
    ∃ (w : List (Fin d)) (μ : ℂ) (φ : Fin D → ℂ),
      w.length ≤ N ∧ μ ≠ 0 ∧ φ ≠ 0 ∧
      evalWord A w *ᵥ φ = μ • φ := by
  obtain ⟨w, hw, htr⟩ := exists_nonzero_trace_word_of_cumulativeSpan_eq_top A hcs
  obtain ⟨μ, φ, hμ, hφ, heig⟩ :=
    _root_.exists_eigenvector_of_trace_ne_zero _ htr
  exact ⟨w, μ, φ, hw, hμ, hφ, heig⟩

/-- If `1 ∈ wordSpan A L`, iterated monotonicity gives
`wordSpan A n ≤ wordSpan A (n + k * L)` for all `k`. -/
theorem wordSpan_mono_mul_of_one_mem_wordSpan
    (A : MPSTensor d D) {L : ℕ}
    (hone : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ wordSpan A L)
    (n k : ℕ) : wordSpan A n ≤ wordSpan A (n + k * L) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc wordSpan A n ≤ wordSpan A (n + k * L) := ih
      _ ≤ wordSpan A (n + k * L + L) :=
          wordSpan_mono_of_one_mem_wordSpan A hone _
      _ = wordSpan A (n + (k + 1) * L) := by ring_nf

end MPSTensor

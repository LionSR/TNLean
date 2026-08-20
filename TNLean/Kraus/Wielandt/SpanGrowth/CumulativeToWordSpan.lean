/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.MatrixNonzeroTraceEigenvalue
import TNLean.Kraus.Wielandt.SpanGrowth.CumulativeSpan

/-!
# From cumulative spans to exact word spans

This file proves transfer-free facts that compare the cumulative span of words
of length at most $n$ with the span of words of length exactly $n$ in a finite
family of square matrices.

If the identity belongs to the one-letter span, exact word spans are monotone,
so the cumulative span at each length equals the corresponding exact word
span. For a unital Kraus family, fullness of one exact word span propagates to
all later lengths.
-/

open scoped Matrix

namespace Kraus

variable {d D : ℕ}

/-- If `cumulativeSpan K N = ⊤` and `D` is nonzero, some word of length at most
`N` has nonzero trace. -/
theorem exists_nonzero_trace_word_of_cumulativeSpan_eq_top [NeZero D]
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) {N : ℕ}
    (hcs : cumulativeSpan K N = ⊤) :
    ∃ w : List (Fin d), w.length ≤ N ∧ Matrix.trace (Kraus.evalWord K w) ≠ 0 := by
  by_contra hall
  push Not at hall
  set trMap : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] ℂ :=
    Matrix.traceLinearMap (Fin D) ℂ ℂ
  have hker : cumulativeSpan K N ≤ LinearMap.ker trMap := by
    apply Submodule.span_le.mpr
    rintro M ⟨w, hw, rfl⟩
    exact LinearMap.mem_ker.mpr (hall w hw)
  have hzero : ∀ M ∈ cumulativeSpan K N, M.trace = 0 :=
    fun M hM => LinearMap.mem_ker.mp (hker hM)
  have hI : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ cumulativeSpan K N :=
    hcs ▸ Submodule.mem_top
  have htrI : (1 : Matrix (Fin D) (Fin D) ℂ).trace ≠ 0 := by
    simp only [Matrix.trace_one, Fintype.card_fin, ne_eq, Nat.cast_eq_zero]
    exact_mod_cast NeZero.ne D
  exact htrI (hzero 1 hI)

/-- Full cumulative span gives a bounded-length word with an eigenvector whose
eigenvalue is nonzero.

Paper anchor: proof of Theorem 1, case (1) in arXiv:0909.5347. -/
theorem exists_eigenvector_of_cumulativeSpan_eq_top [NeZero D]
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) {N : ℕ}
    (hcs : cumulativeSpan K N = ⊤) :
    ∃ (w : List (Fin d)) (μ : ℂ) (φ : Fin D → ℂ),
      w.length ≤ N ∧ μ ≠ 0 ∧ φ ≠ 0 ∧
      Kraus.evalWord K w *ᵥ φ = μ • φ := by
  obtain ⟨w, hw, htr⟩ := exists_nonzero_trace_word_of_cumulativeSpan_eq_top K hcs
  obtain ⟨μ, φ, hμ, hφ, heig⟩ :=
    _root_.exists_eigenvector_of_trace_ne_zero _ htr
  exact ⟨w, μ, φ, hw, hμ, hφ, heig⟩

/-- If the identity belongs to the length-`L` word span, then multiplication by
that identity embeds every length-`n` word span into the length-`n + L` span. -/
theorem wordSpan_mono_of_one_mem_wordSpan
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) {L : ℕ}
    (hone : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ wordSpan K L) :
    ∀ n, wordSpan K n ≤ wordSpan K (n + L) := by
  intro n M hM
  have hmul : M * 1 ∈ wordSpan K n * wordSpan K L :=
    Submodule.mul_mem_mul hM hone
  rw [Matrix.mul_one] at hmul
  rw [wordSpan_add]
  exact hmul

/-- If the identity belongs to the one-letter span, each word span is contained
in its successor. -/
theorem wordSpan_mono_succ_of_one_mem_wordSpan_one
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hone : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ wordSpan K 1) :
    ∀ n, wordSpan K n ≤ wordSpan K (n + 1) :=
  wordSpan_mono_of_one_mem_wordSpan K hone

/-- If the identity belongs to the one-letter span, exact word spans are
monotone in their length. -/
theorem wordSpan_mono'_of_one_mem_wordSpan_one
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hone : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ wordSpan K 1)
    {n m : ℕ} (hnm : n ≤ m) :
    wordSpan K n ≤ wordSpan K m := by
  suffices h : ∀ k, wordSpan K n ≤ wordSpan K (n + k) by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    exact h k
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      wordSpan K n ≤ wordSpan K (n + k) := ih
      _ ≤ wordSpan K (n + k + 1) :=
        wordSpan_mono_succ_of_one_mem_wordSpan_one K hone _
      _ = wordSpan K (n + (k + 1)) := by ring_nf

/-- If a Kraus family is unital and its length-`n` word span is full, then its
length-`n + 1` word span is full. -/
theorem wordSpan_succ_eq_top_of_unital_of_wordSpan_eq_top
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hUnital : ∑ a : Fin d, K a * (K a)ᴴ = 1)
    {n : ℕ} (hTop : wordSpan K n = ⊤) :
    wordSpan K (n + 1) = ⊤ := by
  rw [eq_top_iff]
  intro X _
  have hdecomp : X = ∑ a : Fin d, K a * ((K a)ᴴ * X) := by
    calc
      X = (1 : Matrix (Fin D) (Fin D) ℂ) * X := by simp
      _ = (∑ a : Fin d, K a * (K a)ᴴ) * X := by rw [hUnital]
      _ = ∑ a : Fin d, K a * ((K a)ᴴ * X) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => by rw [Matrix.mul_assoc]
  rw [hdecomp]
  refine Submodule.sum_mem _ fun a _ => ?_
  have hLeft : K a ∈ wordSpan K 1 := by
    simpa [Kraus.evalWord] using
      evalWord_mem_wordSpan K ([a] : List (Fin d))
  have hRight : (K a)ᴴ * X ∈ wordSpan K n := by
    rw [hTop]
    exact Submodule.mem_top
  have hProd : K a * ((K a)ᴴ * X) ∈ wordSpan K 1 * wordSpan K n :=
    Submodule.mul_mem_mul hLeft hRight
  rw [← wordSpan_add] at hProd
  simpa [Nat.add_comm] using hProd

/-- For a unital Kraus family, fullness at length `L` propagates to every
length `m ≥ L`. -/
theorem wordSpan_eq_top_of_ge_of_unital
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hUnital : ∑ a : Fin d, K a * (K a)ᴴ = 1)
    {L m : ℕ} (hL : wordSpan K L = ⊤) (hm : L ≤ m) :
    wordSpan K m = ⊤ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction k with
  | zero => simpa using hL
  | succ k ih =>
    have hPrev : wordSpan K (L + k) = ⊤ := ih (by omega)
    simpa [Nat.add_assoc] using
      wordSpan_succ_eq_top_of_unital_of_wordSpan_eq_top K hUnital hPrev

/-- If the identity belongs to the one-letter span, the cumulative span at each
length equals the exact word span at that length. -/
theorem cumulativeSpan_eq_wordSpan_of_one_mem_wordSpan_one
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hone : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ wordSpan K 1) :
    ∀ n, cumulativeSpan K n = wordSpan K n := by
  intro n
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro M ⟨w, hw, rfl⟩
    exact wordSpan_mono'_of_one_mem_wordSpan_one K hone hw
      (evalWord_mem_wordSpan K w)
  · exact wordSpan_le_cumulativeSpan K (le_refl n)

end Kraus

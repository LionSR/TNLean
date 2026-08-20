/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Kraus.Injectivity
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Cumulative spans of words in a finite Kraus family

This file defines the cumulative span of all products of at most a prescribed
length and proves its elementary growth and stabilization properties. The
construction depends only on a finite family of square matrices.

The exact-length spaces `Kraus.wordSpan` are the spaces denoted by $S_n$ in
Sanz, Pérez-García, Wolf, and Cirac, arXiv:0909.5347, equation (1). The spaces
`Kraus.cumulativeSpan` are the cumulative spaces $T_n$ used in the proof of
Lemma 1.
-/

open scoped Matrix

namespace Kraus

variable {d D : ℕ}

/-- Evaluation of a nonempty word splits into its first letter and remaining suffix. -/
theorem evalWord_ofFn_succ (K : Fin d → Matrix (Fin D) (Fin D) ℂ) {n : ℕ}
    (σ : Fin (n + 1) → Fin d) :
    MPSTensor.evalWord K (List.ofFn σ) =
      K (σ 0) * MPSTensor.evalWord K (List.ofFn (σ ∘ Fin.succ)) := by
  rw [List.ofFn_succ]
  rfl

/-- Every word of length `n + 1` belongs to the product of the one-letter span
and the length-`n` word span. -/
theorem wordSpan_succ_le_mul (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (n : ℕ) :
    wordSpan K (n + 1) ≤
      Submodule.span ℂ (Set.range K) * wordSpan K n := by
  rw [← wordSpan_one K, ← wordSpan_add K 1 n, Nat.one_add]

/-- The length-`n + 1` word span factors by its first letter. -/
theorem wordSpan_succ_eq_mul_left
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (n : ℕ) :
    wordSpan K (n + 1) =
      Submodule.span ℂ (Set.range K) * wordSpan K n := by
  rw [← wordSpan_one K, ← wordSpan_add K 1 n, Nat.one_add]

/-- The span of all products of at most `n` matrices from a finite Kraus family. -/
def cumulativeSpan (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (n : ℕ) :
    Submodule ℂ (Matrix (Fin D) (Fin D) ℂ) :=
  Submodule.span ℂ
    {X | ∃ w : List (Fin d), w.length ≤ n ∧ X = MPSTensor.evalWord K w}

/-- An evaluated word of length at most `n` belongs to `cumulativeSpan K n`. -/
theorem mem_cumulativeSpan_generator
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) {n : ℕ}
    {w : List (Fin d)} (hw : w.length ≤ n) :
    MPSTensor.evalWord K w ∈ cumulativeSpan K n :=
  Submodule.subset_span ⟨w, hw, rfl⟩

/-- An exact word span is contained in every sufficiently large cumulative span. -/
theorem wordSpan_le_cumulativeSpan
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) {m n : ℕ} (h : m ≤ n) :
    wordSpan K m ≤ cumulativeSpan K n := by
  apply Submodule.span_le.mpr
  rintro X ⟨σ, rfl⟩
  change MPSTensor.evalWord K (List.ofFn σ) ∈ _
  apply mem_cumulativeSpan_generator
  simpa only [List.length_ofFn]

/-- Cumulative word spans increase with the length bound. -/
theorem cumulativeSpan_mono
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (n : ℕ) :
    cumulativeSpan K n ≤ cumulativeSpan K (n + 1) := by
  apply Submodule.span_mono
  rintro X ⟨w, hw, rfl⟩
  exact ⟨w, by omega, rfl⟩

/-- Cumulative word spans are monotone in their length bound. -/
theorem cumulativeSpan_mono'
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) {n m : ℕ} (h : n ≤ m) :
    cumulativeSpan K n ≤ cumulativeSpan K m := by
  apply Submodule.span_mono
  rintro X ⟨w, hw, rfl⟩
  exact ⟨w, hw.trans h, rfl⟩

/-- If all words of length `n + 1` already lie in `cumulativeSpan K n`, then
left multiplication by a Kraus matrix preserves that space. -/
theorem left_mul_mem_cumulativeSpan
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) {n : ℕ}
    (hstab : wordSpan K (n + 1) ≤ cumulativeSpan K n)
    (i : Fin d) (X : Matrix (Fin D) (Fin D) ℂ)
    (hX : X ∈ cumulativeSpan K n) :
    K i * X ∈ cumulativeSpan K n := by
  have hmul : Submodule.map (LinearMap.mulLeft ℂ (K i))
      (cumulativeSpan K n) ≤ cumulativeSpan K n := by
    rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, rfl⟩
    change (LinearMap.mulLeft ℂ (K i)) (MPSTensor.evalWord K w) ∈
      cumulativeSpan K n
    simp only [LinearMap.mulLeft_apply]
    change MPSTensor.evalWord K (i :: w) ∈ cumulativeSpan K n
    by_cases hle : w.length + 1 ≤ n
    · exact mem_cumulativeSpan_generator K (by simpa)
    · have hlen : (i :: w).length = n + 1 := by
        simp
        omega
      have hmem := evalWord_mem_wordSpan K (i :: w)
      rw [hlen] at hmem
      exact hstab hmem
  exact hmul ⟨X, hX, by simp [LinearMap.mulLeft_apply]⟩

/-- Once two consecutive cumulative word spans agree, every later cumulative
word span agrees with them. -/
theorem cumulativeSpan_stable
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) {n : ℕ}
    (h : cumulativeSpan K n = cumulativeSpan K (n + 1)) :
    ∀ m, n ≤ m → cumulativeSpan K m = cumulativeSpan K n := by
  have hstab : wordSpan K (n + 1) ≤ cumulativeSpan K n := by
    calc
      wordSpan K (n + 1) ≤ cumulativeSpan K (n + 1) :=
        wordSpan_le_cumulativeSpan K le_rfl
      _ = cumulativeSpan K n := h.symm
  have hword_all : ∀ w : List (Fin d), n < w.length →
      MPSTensor.evalWord K w ∈ cumulativeSpan K n := by
    intro w hw
    induction w with
    | nil => simp at hw
    | cons i w ih =>
      simp only [MPSTensor.evalWord]
      by_cases hw' : n < w.length
      · exact left_mul_mem_cumulativeSpan K hstab i _ (ih hw')
      · have hmem : MPSTensor.evalWord K w ∈ cumulativeSpan K n :=
          mem_cumulativeSpan_generator K (by omega)
        exact left_mul_mem_cumulativeSpan K hstab i _ hmem
  intro m hm
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, rfl⟩
    by_cases hw' : w.length ≤ n
    · exact mem_cumulativeSpan_generator K hw'
    · exact hword_all w (by omega)
  · exact cumulativeSpan_mono' K hm

/-- The dimension of a cumulative word span is at most `D ^ 2`. -/
theorem cumulativeSpan_finrank_le
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (n : ℕ) :
    Module.finrank ℂ (cumulativeSpan K n) ≤ D ^ 2 := by
  calc
    Module.finrank ℂ (cumulativeSpan K n) ≤
        Module.finrank ℂ (Matrix (Fin D) (Fin D) ℂ) :=
      Submodule.finrank_le _
    _ = D ^ 2 := by
      rw [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one]
      ring

/-- Strict growth of cumulative word spans gives strict growth of dimensions. -/
theorem cumulativeSpan_finrank_strict_mono
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) {n : ℕ}
    (h : cumulativeSpan K n < cumulativeSpan K (n + 1)) :
    Module.finrank ℂ (cumulativeSpan K n) <
      Module.finrank ℂ (cumulativeSpan K (n + 1)) := by
  let _ : FiniteDimensional ℂ ↥(cumulativeSpan K (n + 1)) :=
    FiniteDimensional.finiteDimensional_submodule _
  exact Submodule.finrank_lt_finrank_of_lt h

/-- The identity matrix belongs to every cumulative word span. -/
theorem one_mem_cumulativeSpan
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (n : ℕ) :
    (1 : Matrix (Fin D) (Fin D) ℂ) ∈ cumulativeSpan K n :=
  Submodule.subset_span ⟨[], by simp, by simp [MPSTensor.evalWord]⟩

/-- Zero-length words do not span the full matrix algebra when `2 ≤ D`. -/
theorem wordSpan_zero_ne_top_of_two_le [NeZero D]
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (hD : 2 ≤ D) :
    wordSpan K 0 ≠ (⊤ : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ)) := by
  intro h
  have h1 : Module.finrank ℂ (wordSpan K 0) = 1 := by
    rw [wordSpan_zero, finrank_span_singleton one_ne_zero]
  rw [h, finrank_top] at h1
  simp only [Module.finrank_matrix, Fintype.card_fin,
    Module.finrank_self, mul_one] at h1
  have hfour : 2 * 2 ≤ D * D := Nat.mul_le_mul hD hD
  omega

end Kraus

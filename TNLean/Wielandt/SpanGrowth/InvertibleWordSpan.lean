/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Kraus.Wielandt.SpanGrowth.InvertibleWordSpan
import TNLean.Wielandt.Primitivity.Definitions
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Invertible-element word span growth for MPS tensors

This file preserves the established `MPSTensor` interface to finite-family
word-span growth. The underlying algebra is stated in `namespace Kraus` and
uses `Kraus.HasEventuallyFullWordSpan` directly. The MPS-specific rank,
normality, and index consequences remain here.
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- The dimension of `wordSpan A n` is bounded by `D²`. -/
theorem wordSpan_finrank_le (A : MPSTensor d D) (n : ℕ) :
    Module.finrank ℂ (wordSpan A n) ≤ D ^ 2 :=
  Kraus.wordSpan_finrank_le A n

/-- A length-one word evaluates to the corresponding tensor entry. -/
theorem evalWord_ofFn_one_eq (A : MPSTensor d D) (σ : Fin 1 → Fin d) :
    evalWord A (List.ofFn σ) = A (σ 0) :=
  Kraus.evalWord_ofFn_one_eq A σ

/-- Every tensor entry belongs to the one-step word span. -/
theorem apply_mem_wordSpan_one (A : MPSTensor d D) (i : Fin d) :
    A i ∈ wordSpan A 1 :=
  Kraus.apply_mem_wordSpan_one A i

/-- Add a one-step span element as a redundant first generator. -/
abbrev oneStepAugment (A : MPSTensor d D)
    (X : Matrix (Fin D) (Fin D) ℂ) : MPSTensor (d + 1) D :=
  Kraus.oneStepAugment A X

@[simp] theorem oneStepAugment_zero (A : MPSTensor d D)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    oneStepAugment A X 0 = X :=
  Kraus.oneStepAugment_zero A X

@[simp] theorem oneStepAugment_succ (A : MPSTensor d D)
    (X : Matrix (Fin D) (Fin D) ℂ) (i : Fin d) :
    oneStepAugment A X i.succ = A i :=
  Kraus.oneStepAugment_succ A X i

/-- Every entry of the augmented tensor lies in the original one-step span
when the new first entry does. -/
theorem oneStepAugment_apply_mem_wordSpan_one (A : MPSTensor d D)
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : X ∈ wordSpan A 1)
    (i : Fin (d + 1)) :
    oneStepAugment A X i ∈ wordSpan A 1 :=
  Kraus.oneStepAugment_apply_mem_wordSpan_one A hX i

/-- Adding an element of `wordSpan A 1` does not change the one-step span. -/
theorem wordSpan_oneStepAugment_one (A : MPSTensor d D)
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : X ∈ wordSpan A 1) :
    wordSpan (oneStepAugment A X) 1 = wordSpan A 1 :=
  Kraus.wordSpan_oneStepAugment_one A hX

/-- Adding an element of `wordSpan A 1` does not change any exact word span. -/
theorem wordSpan_oneStepAugment_eq (A : MPSTensor d D)
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : X ∈ wordSpan A 1) (n : ℕ) :
    wordSpan (oneStepAugment A X) n = wordSpan A n :=
  Kraus.wordSpan_oneStepAugment_eq A hX n

/-- Normality is unchanged after adding a redundant one-step generator. -/
theorem isNormal_oneStepAugment_of_mem_wordSpan_one (A : MPSTensor d D)
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : X ∈ wordSpan A 1)
    (hN : IsNormal A) :
    IsNormal (oneStepAugment A X) := by
  obtain ⟨N, hNpos, hNtop⟩ := (hasEventuallyFullKrausRank_iff_isNormal A).2 hN
  exact (hasEventuallyFullKrausRank_iff_isNormal (oneStepAugment A X)).1
    ⟨N, hNpos, by simpa [wordSpan_oneStepAugment_eq A hX N] using hNtop⟩

/-- The Kraus rank is unchanged after adding a redundant one-step generator. -/
theorem krausRank_oneStepAugment (A : MPSTensor d D)
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : X ∈ wordSpan A 1) :
    krausRank (oneStepAugment A X) = krausRank A := by
  unfold krausRank
  rw [wordSpan_oneStepAugment_eq A hX 1]

/-- Left multiplication by `A i₀` maps `wordSpan A n` into the next span. -/
theorem mulLeft_image_wordSpan_le_succ (A : MPSTensor d D)
    (i₀ : Fin d) (n : ℕ) :
    Submodule.map (LinearMap.mulLeft ℂ (A i₀)) (wordSpan A n) ≤
      wordSpan A (n + 1) :=
  Kraus.mulLeft_image_wordSpan_le_succ A i₀ n

/-- Left multiplication by `A i₀ ^ k` advances a word span by `k` levels. -/
theorem mulLeft_pow_image_wordSpan_le (A : MPSTensor d D)
    (i₀ : Fin d) (n k : ℕ) :
    Submodule.map (LinearMap.mulLeft ℂ (A i₀ ^ k)) (wordSpan A n) ≤
      wordSpan A (n + k) :=
  Kraus.mulLeft_pow_image_wordSpan_le A i₀ n k

/-- An invertible tensor entry makes the dimensions of consecutive word spans
nondecreasing. -/
theorem wordSpan_finrank_mono_of_isUnit (A : MPSTensor d D)
    (i₀ : Fin d) (hU : IsUnit (A i₀)) (n : ℕ) :
    Module.finrank ℂ (wordSpan A n) ≤
      Module.finrank ℂ (wordSpan A (n + 1)) :=
  Kraus.wordSpan_finrank_mono_of_isUnit A i₀ hU n

/-- An invertible tensor entry makes word-span dimension monotone in the word
length. -/
theorem wordSpan_finrank_mono_of_isUnit' (A : MPSTensor d D)
    (i₀ : Fin d) (hU : IsUnit (A i₀)) {m n : ℕ} (h : m ≤ n) :
    Module.finrank ℂ (wordSpan A m) ≤ Module.finrank ℂ (wordSpan A n) :=
  Kraus.wordSpan_finrank_mono_of_isUnit' A i₀ hU h

/-- If one word span is full and a tensor entry is invertible, every later
word span is full. -/
theorem wordSpan_eq_top_of_ge_of_isUnit (A : MPSTensor d D)
    (i₀ : Fin d) (hU : IsUnit (A i₀)) {N : ℕ}
    (hN : wordSpan A N = ⊤) {m : ℕ} (hm : N ≤ m) :
    wordSpan A m = ⊤ :=
  Kraus.wordSpan_eq_top_of_ge_of_isUnit A i₀ hU hN hm

/-- Right multiplication by `A i₀` maps `wordSpan A n` into the next span. -/
theorem mulRight_image_wordSpan_le_succ (A : MPSTensor d D)
    (i₀ : Fin d) (n : ℕ) :
    Submodule.map (LinearMap.mulRight ℂ (A i₀)) (wordSpan A n) ≤
      wordSpan A (n + 1) :=
  Kraus.mulRight_image_wordSpan_le_succ A i₀ n

/-- Equality of consecutive dimensions identifies the next span with the
right-multiplication image of the preceding span. -/
theorem wordSpan_succ_eq_mulRight_image_of_finrank_eq (A : MPSTensor d D)
    (i₀ : Fin d) (hU : IsUnit (A i₀)) (r : ℕ)
    (hfin : Module.finrank ℂ (wordSpan A r) =
      Module.finrank ℂ (wordSpan A (r + 1))) :
    wordSpan A (r + 1) =
      Submodule.map (LinearMap.mulRight ℂ (A i₀)) (wordSpan A r) :=
  Kraus.wordSpan_succ_eq_mulRight_image_of_finrank_eq A i₀ hU r hfin

/-- Equality of consecutive dimensions bounds every later word span by a
right-multiplication image of the stabilized span. -/
theorem wordSpan_le_mulRight_pow_image (A : MPSTensor d D)
    (i₀ : Fin d) (hU : IsUnit (A i₀)) (r k : ℕ)
    (hfin : Module.finrank ℂ (wordSpan A r) =
      Module.finrank ℂ (wordSpan A (r + 1))) :
    wordSpan A (r + k) ≤
      Submodule.map (LinearMap.mulRight ℂ (A i₀ ^ k)) (wordSpan A r) :=
  Kraus.wordSpan_le_mulRight_pow_image A i₀ hU r k hfin

private theorem hasEventuallyFullWordSpan_of_isNormal_of_isUnit
    (A : MPSTensor d D) (i₀ : Fin d) (hU : IsUnit (A i₀))
    (hN : IsNormal A) : Kraus.HasEventuallyFullWordSpan A := by
  obtain ⟨N, _hNpos, hNtop⟩ := (hasEventuallyFullKrausRank_iff_isNormal A).2 hN
  exact Filter.eventually_atTop.mpr
    ⟨N, fun m hm => Kraus.wordSpan_eq_top_of_ge_of_isUnit A i₀ hU hNtop hm⟩

/-- Under normality and an invertible tensor entry, word-span dimensions grow
strictly until they reach `D²`. -/
theorem wordSpan_finrank_strict_mono_of_isUnit_of_isNormal
    (A : MPSTensor d D) (i₀ : Fin d)
    (hU : IsUnit (A i₀)) (hN : IsNormal A) (n : ℕ)
    (hlt : Module.finrank ℂ (wordSpan A n) < D ^ 2) :
    Module.finrank ℂ (wordSpan A n) <
      Module.finrank ℂ (wordSpan A (n + 1)) :=
  Kraus.wordSpan_finrank_strict_mono_of_isUnit_of_hasEventuallyFullWordSpan
    A i₀ hU (hasEventuallyFullWordSpan_of_isNormal_of_isUnit A i₀ hU hN) n hlt

/-- If an MPS tensor is normal and has an invertible entry, then the exact
word span at level `D² - krausRank A + 1` is full.

Paper: arXiv:0909.5347, Theorem 1 case (2); Wolf, Theorem 6.9. -/
theorem wordSpan_eq_top_of_isNormal_of_isUnit (A : MPSTensor d D)
    (i₀ : Fin d) (hU : IsUnit (A i₀)) (hN : IsNormal A) :
    wordSpan A (D ^ 2 - krausRank A + 1) = ⊤ := by
  unfold krausRank wordSpan
  exact Kraus.wordSpan_eq_top_of_hasEventuallyFullWordSpan_of_isUnit A i₀ hU
    (hasEventuallyFullWordSpan_of_isNormal_of_isUnit A i₀ hU hN)

/-- The invertible-case numerical bound on the full-Kraus-rank index.

Paper: arXiv:0909.5347, Theorem 1 case (2); Wolf, Theorem 6.9. -/
theorem iIndex_le_of_isNormal_of_isUnit (A : MPSTensor d D)
    (i₀ : Fin d) (hU : IsUnit (A i₀)) (hN : IsNormal A) :
    iIndex A ≤ D ^ 2 - krausRank A + 1 := by
  rw [iIndex]
  exact Nat.sInf_le ⟨by omega,
    wordSpan_eq_top_of_isNormal_of_isUnit A i₀ hU hN⟩

end MPSTensor

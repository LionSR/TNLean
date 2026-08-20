/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Kraus.WordSpan

/-!
# Bounded rank-one element in a word span

This file introduces the two-sided span

`biRectSpan P Q K n = span{ P * M * Q : M ∈ wordSpan K n }`

for a finite family of square matrices. If the exact word span is full, this
space is the full range of the map $X \mapsto PXQ$. If `P` and `Q` belong to
bounded word spans, every element of the two-sided span belongs to a bounded
word span.
-/

open scoped Matrix

namespace Kraus

variable {d D : ℕ}

/-- The image of `wordSpan K n` under the map $X \mapsto PXQ$. -/
noncomputable def biRectSpan
    (P Q : Matrix (Fin D) (Fin D) ℂ)
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (n : ℕ) :
    Submodule ℂ (Matrix (Fin D) (Fin D) ℂ) :=
  Submodule.map ((LinearMap.mulLeft ℂ P).comp (LinearMap.mulRight ℂ Q))
    (wordSpan K n)

/-- If the exact word span is full, the two-sided span is the full range of
$X \mapsto PXQ$. -/
theorem biRectSpan_eq_range_of_wordSpan_eq_top
    (P Q : Matrix (Fin D) (Fin D) ℂ)
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) {n : ℕ}
    (htop : wordSpan K n = ⊤) :
    biRectSpan P Q K n =
      LinearMap.range ((LinearMap.mulLeft ℂ P).comp (LinearMap.mulRight ℂ Q)) := by
  rw [biRectSpan, htop, Submodule.map_top]

private theorem mem_biRectSpan_iff
    (P Q : Matrix (Fin D) (Fin D) ℂ)
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) {n : ℕ}
    {M : Matrix (Fin D) (Fin D) ℂ} :
    M ∈ biRectSpan P Q K n ↔
      ∃ X, X ∈ wordSpan K n ∧ P * X * Q = M := by
  constructor
  · intro hM
    rcases Submodule.mem_map.mp hM with ⟨X, hX, rfl⟩
    exact ⟨X, hX, by
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
        Matrix.mul_assoc]⟩
  · rintro ⟨X, hX, hM⟩
    rw [← hM]
    exact Submodule.mem_map.mpr ⟨X, hX, by
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
        Matrix.mul_assoc]⟩

/-- If `P` and `Q` belong to word spans of lengths `m₁` and `m₂`, respectively,
then the two-sided span generated from words of length `n` lies in the word
span of length `m₁ + n + m₂`. -/
theorem biRectSpan_le_wordSpan
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) {m₁ m₂ n : ℕ}
    (P Q : Matrix (Fin D) (Fin D) ℂ)
    (hP : P ∈ wordSpan K m₁) (hQ : Q ∈ wordSpan K m₂) :
    biRectSpan P Q K n ≤ wordSpan K (m₁ + n + m₂) := by
  intro M hM
  rcases (mem_biRectSpan_iff P Q K).mp hM with ⟨Y, hY, rfl⟩
  have hPY : P * Y ∈ wordSpan K (m₁ + n) := by
    rw [wordSpan_add]
    exact Submodule.mul_mem_mul hP hY
  rw [wordSpan_add]
  exact Submodule.mul_mem_mul hPY hQ

end Kraus

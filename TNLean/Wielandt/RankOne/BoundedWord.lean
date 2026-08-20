/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Kraus.Wielandt.RankOne.BoundedWord
import TNLean.Wielandt.SpanGrowth.CumulativeSpan

/-!
# Bounded rank-one element in a blocked word span

This file restates the `Kraus` two-sided word-span results using the `MPSTensor`
word-span notation.
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- Two-sided word span for an MPS tensor. -/
noncomputable def biRectSpan
    (P Q : Matrix (Fin D) (Fin D) ℂ) (B : MPSTensor d D) (n : ℕ) :
    Submodule ℂ (Matrix (Fin D) (Fin D) ℂ) :=
  Kraus.biRectSpan P Q B n

/-- If the exact word span is full, the two-sided span is the full range of
$X \mapsto PXQ$. -/
theorem biRectSpan_eq_range_of_wordSpan_eq_top
    (P Q : Matrix (Fin D) (Fin D) ℂ) (B : MPSTensor d D) {n : ℕ}
    (htop : wordSpan B n = ⊤) :
    biRectSpan (d := d) (D := D) P Q B n =
      LinearMap.range ((LinearMap.mulLeft ℂ P).comp (LinearMap.mulRight ℂ Q)) :=
  Kraus.biRectSpan_eq_range_of_wordSpan_eq_top P Q B htop

/-- If the two outer matrices belong to bounded word spans, the two-sided span
is contained in the word span at the sum of the three lengths. -/
theorem biRectSpan_le_wordSpan
    (B : MPSTensor d D) {m₁ m₂ n : ℕ}
    (P Q : Matrix (Fin D) (Fin D) ℂ)
    (hP : P ∈ wordSpan B m₁) (hQ : Q ∈ wordSpan B m₂) :
    biRectSpan (d := d) (D := D) P Q B n ≤ wordSpan B (m₁ + n + m₂) :=
  Kraus.biRectSpan_le_wordSpan B P Q hP hQ

end MPSTensor

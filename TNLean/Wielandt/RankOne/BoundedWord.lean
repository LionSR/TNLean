/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Wielandt.RankOne.Manufacture
import TNLean.Wielandt.SpanGrowth.CumulativeSpan
import TNLean.Wielandt.SpanGrowth.VectorToMatrixSpan

/-!
# Bounded rank-one element in a blocked word span (Wielandt Lemma 2(b))

This file introduces a two-sided ("bi-rectangular") span

`biRectSpan P Q B n = span{ P * M * Q : M ∈ wordSpan B n }`

and develops the membership and conversion lemmas used by the rank-one
extraction step in the Quantum Wielandt proof: if the exact word span is
already full, the bi-rectangular span is the full two-sided range of the
linear map `X ↦ P * X * Q` (`biRectSpan_eq_range_of_wordSpan_eq_top`), and if
`P` and `Q` themselves lie in bounded word spans, the bi-rectangular span is
contained in a bounded word span (`biRectSpan_le_wordSpan`).
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- Two-sided (bi-rectangular) span: image of `wordSpan B n` under right-multiplication by `Q`
followed by left-multiplication by `P`.

This is the linear span of all matrices of the form `P * M * Q` where
`M` ranges over word products of length `n`. -/
noncomputable def biRectSpan
    (P Q : Matrix (Fin D) (Fin D) ℂ) (B : MPSTensor d D) (n : ℕ) :
    Submodule ℂ (Matrix (Fin D) (Fin D) ℂ) :=
  Submodule.map ((LinearMap.mulLeft ℂ P).comp (LinearMap.mulRight ℂ Q))
    (wordSpan B n)

/-- If the exact word span is already full, the bi-rectangular span is the full two-sided
range. -/
theorem biRectSpan_eq_range_of_wordSpan_eq_top
    (P Q : Matrix (Fin D) (Fin D) ℂ) (B : MPSTensor d D) {n : ℕ}
    (htop : wordSpan B n = ⊤) :
    biRectSpan (d := d) (D := D) P Q B n =
      LinearMap.range ((LinearMap.mulLeft ℂ P).comp (LinearMap.mulRight ℂ Q)) := by
  rw [biRectSpan, htop, Submodule.map_top]

private theorem mem_biRectSpan_iff
    (P Q : Matrix (Fin D) (Fin D) ℂ) (B : MPSTensor d D) {n : ℕ}
    {M : Matrix (Fin D) (Fin D) ℂ} :
    M ∈ biRectSpan (d := d) (D := D) P Q B n ↔
      ∃ X, X ∈ wordSpan B n ∧ P * X * Q = M := by
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

/-- Converting a bi-rectangular span element back into a bounded word span,
assuming `P` and `Q` themselves lie in bounded word spans. -/
theorem biRectSpan_le_wordSpan
    (B : MPSTensor d D) {m₁ m₂ n : ℕ}
    (P Q : Matrix (Fin D) (Fin D) ℂ)
    (hP : P ∈ wordSpan B m₁) (hQ : Q ∈ wordSpan B m₂) :
    biRectSpan (d := d) (D := D) P Q B n ≤ wordSpan B (m₁ + n + m₂) := by
  classical
  intro M hM
  rcases (mem_biRectSpan_iff (d := d) (D := D) P Q B).mp hM with ⟨Y, hY, hM⟩
  have hPY : P * Y ∈ wordSpan B (m₁ + n) := by
    exact (wordSpan_mul_le B m₁ n) (Submodule.mul_mem_mul hP hY)
  have hPYQ : (P * Y) * Q ∈ wordSpan B ((m₁ + n) + m₂) := by
    exact (wordSpan_mul_le B (m₁ + n) m₂) (Submodule.mul_mem_mul hPY hQ)
  rw [← hM]
  simpa only [Matrix.mul_assoc, Nat.add_assoc] using hPYQ

end MPSTensor

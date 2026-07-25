/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Wielandt.RectangularSpan.UniversalityAux.Basic

/-!
# Rectangular span universality auxiliary lemmas: quantitative ceiling

This module contains the Section 8e dimension-counting results for rectangular
spans, including the quantitative cumulative-span range equality and the
parametric Wielandt-length bounds derived from a stabilization witness.
-/

open scoped Matrix

namespace MPSTensor

/-! ## Section 8e: Quantitative ceiling for one-sided rectangular span

This section provides the quantitative dimension-counting lemmas for the
exact Lemma 2(b) bound. The key results are:

1. **Level zero**: `rectSpan P A 0 = span{P}` (`rectSpan_zero_eq_span`).
2. **Tight ceiling**: `finrank(rectSpan P A n) ≤ D · rank(P)`, matching the exact formula
   `finrank(range(mulLeft P)) = D · rank(P)` from `RectangularSpan/Ranges.lean`.
3. **Quantitative range equality**: `cumulativeRectSpan_eq_range_quantitative`.
4. **Parametric Wielandt-length bound**: `wielandt_parametric_span`, combining a `rectSpan`
   stabilization witness with the conditional Lemma 2(b) rank-one step.

These results are designed to combine with the already proved `vecMulVec_eigenvector_mem_wordSpan`
to give the quantitative stage bound on the Wolf/paper path toward `D²-D+1`.

### References
- arXiv:0909.5347, Lemma 2(b)
- Wolf, "Quantum Channels & Operations", Section 6.2.4
-/

section QuantitativeCeiling

open Matrix Module

variable {d D : ℕ}

/-! ### Part 1: Initial dimension of rectSpan -/

/-- `rectSpan P A 0 = span{P}`: the level-0 rectangular span is just the 1-D subspace
spanned by `P` (since `wordSpan A 0 = span{1}`). -/
theorem rectSpan_zero_eq_span (P : Matrix (Fin D) (Fin D) ℂ) (A : MPSTensor d D) :
    rectSpan P A 0 = Submodule.span ℂ {P} := by
  simp only [rectSpan, wordSpan_zero]
  rw [Submodule.map_span]
  congr 1
  ext M
  simp only [Set.mem_image, Set.mem_singleton_iff, LinearMap.mulLeft_apply]
  constructor
  · rintro ⟨N, rfl, rfl⟩; simp
  · intro hM; exact ⟨1, rfl, by simp [hM]⟩

/-! ### Part 2: Tight ceiling for rectSpan finrank -/

/-- **Tight ceiling**: `finrank(rectSpan P A n) ≤ D * rank(P)`.

This improves the generic bound `≤ D²` when `rank(P) < D`, which is the case
when `P = (A i₀)^D` and `A i₀` is not invertible. -/
theorem rectSpan_finrank_le_rank_mul_D (P : Matrix (Fin D) (Fin D) ℂ)
    (A : MPSTensor d D) (n : ℕ) :
    finrank ℂ (rectSpan P A n) ≤ D * P.rank := by
  calc finrank ℂ (rectSpan P A n)
      ≤ finrank ℂ (LinearMap.range (LinearMap.mulLeft ℂ P)) :=
        Submodule.finrank_mono (rectSpan_le_range P A n)
    _ = D * P.rank := finrank_range_mulLeft P

/-! ### Part 3: Quantitative cumulative rectangular span = range -/

/-- **Quantitative cumulativeRectSpan = range under IsNormal.**

Under `[NeZero D]` and `IsNormal A`, the cumulative rectangular span at level `D²` equals
the full range of left-multiplication by `P`.

This follows from `cumulativeSpan A (D²) = ⊤` (which is
`cumulativeSpan_eq_top_of_isNormal_bound`). -/
theorem cumulativeRectSpan_eq_range_quantitative [NeZero D]
    (P : Matrix (Fin D) (Fin D) ℂ) (A : MPSTensor d D)
    (hN : IsNormal A) :
    cumulativeRectSpan P A (D ^ 2) = LinearMap.range (LinearMap.mulLeft ℂ P) := by
  exact cumulativeRectSpan_eq_range_of_isNormal P A hN

/-! ### Part 4: Parametric rectangular span — toward exact Lemma 2(b)

The parametric rectangular span theorem combines:
1. Power membership: `(A i₀)^D ∈ wordSpan A D`
2. Eigenvector in range: `φ ∈ range(toLin' ((A i₀)^D))`
3. Stabilization: `rectSpan ((A i₀)^D) A n₀ = range(mulLeft ((A i₀)^D))`
4. Transfer: `vecMulVec φ ψ ∈ wordSpan A (D + n₀)`
5. Conditional fixed-length matrix spanning: `wordSpan A (D + n₀ + 2(D-1)) = ⊤`

into a single theorem parameterized by the stabilization witness `n₀`.

When the Wielandt inductive bound is available (giving `n₀ ≤ D² - 3D + 3`),
this yields `wordSpan A (D² - D + 1) = ⊤`.
-/

/-- **Parametric Lemma 2(b) (rectangular span).**

Given the full eigenvector/row-eigenvector setup AND a stabilization witness `n₀`
such that `rectSpan ((A i₀)^D) A n₀ = range(mulLeft ((A i₀)^D))`, we get:

  `wordSpan A (D + n₀ + 2*(D-1)) = ⊤`

i.e., the word span at length `D + n₀ + 2D - 2` is the full matrix algebra.

### Proof strategy
1. Eigenvector `φ` lies in `range(toLin' ((A i₀)^D))`, so for all `ψ`,
   `vecMulVec φ ψ ∈ rectSpan`.
2. `rectSpan` stabilized at `n₀` → `vecMulVec φ ψ ∈ wordSpan A (D + n₀)`
3. Apply conditional fixed-length matrix spanning (eigenvector spreading + row spreading)
4. Output: `wordSpan A ((D-1) + ((D + n₀) + (D-1))) = ⊤`

This simplifies to `wordSpan A (3D + n₀ - 2) = ⊤`.

The hypothesis `n₀` is the key degree of freedom. Different bounds on `n₀`
give different final bounds:
- `n₀ = D² - 2D + 2` (normality witness): gives `D² + D = ⊤` (coarse)
- `n₀ = D² - 4D + 3` (from induction on D): gives `D² - D + 1 = ⊤` (sharp) -/
theorem wielandt_parametric_span [NeZero D]
    (A : MPSTensor d D)
    (hNormal : IsNormal (d := d) (D := D) A)
    -- Column eigenvector
    (i₀ : Fin d) (μ : ℂ) (hμ : μ ≠ 0)
    (φ : Fin D → ℂ) (hφ : φ ≠ 0)
    (heigφ : A i₀ *ᵥ φ = μ • φ)
    -- Row eigenvector (for the conditional fixed-length matrix spanning)
    (i₁ : Fin d) (ν : ℂ) (hν : ν ≠ 0)
    (ψ₀ : Fin D → ℂ) (hψ₀ : ψ₀ ≠ 0)
    (heigψ : (A i₁)ᵀ *ᵥ ψ₀ = ν • ψ₀)
    -- Stabilization witness
    {n₀ : ℕ}
    (hstab : rectSpan ((A i₀) ^ D) A n₀ =
             LinearMap.range (LinearMap.mulLeft ℂ ((A i₀) ^ D))) :
    wordSpan A ((D - 1) + ((D + n₀) + (D - 1))) = ⊤ := by
  -- Step 1: vecMulVec φ ψ₀ ∈ wordSpan A (D + n₀)
  have hRankOne : vecMulVec φ ψ₀ ∈ wordSpan A (D + n₀) :=
    vecMulVec_eigenvector_mem_wordSpan A i₀ hμ heigφ hstab ψ₀
  -- Step 2: Apply conditional fixed-length matrix spanning
  exact wielandt_lemma2b_conditional A hNormal i₀ μ hμ φ hφ heigφ
    i₁ ν hν ψ₀ hψ₀ heigψ hRankOne

end QuantitativeCeiling

end MPSTensor

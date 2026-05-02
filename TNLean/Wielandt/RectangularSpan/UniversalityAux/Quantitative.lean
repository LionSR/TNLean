/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/

import TNLean.Wielandt.RectangularSpan.UniversalityAux.Basic

/-!
# Rectangular span universality auxiliary lemmas: quantitative ceiling

This module contains the Section 8e dimension-counting results for rectangular
spans, including the quantitative cumulative-span transfer and the parametric
Wielandt-length bounds derived from a stabilization witness.
-/

open scoped Matrix

namespace MPSTensor

/-! ## Section 8e: Quantitative ceiling for one-sided rectangular span

This section provides the quantitative dimension-counting infrastructure for the
exact Lemma 2(b) bound. The key results are:

1. **Initial dimension**: `rectSpan P A 0` has finrank 1 when `P ≠ 0` (it equals `span{P}`).
2. **Tight ceiling**: `finrank(rectSpan P A n) ≤ D · rank(P)`, matching the exact formula
   `finrank(range(mulLeft P)) = D · rank(P)` from `RectangularRanges.lean`.
3. **Tight pigeonhole**: finrank stabilization within `D · rank(P)` steps (vs `D²`).
4. **Cumulative transfer**: `cumulativeRectSpan` to `cumulativeSpan` level shift.
5. **Quantitative eigenvector rank-one**: under `IsNormal` + eigenvector, every rank-one
   `vecMulVec φ ψ` lies in `cumulativeSpan A (D + D²)`.

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

/-- `wordSpan A 0 = span{1}`: words of length 0 consist only of the identity. -/
private theorem wordSpan_zero_eq (A : MPSTensor d D) :
    wordSpan A 0 = Submodule.span ℂ {(1 : Matrix (Fin D) (Fin D) ℂ)} := by
  -- wordSpan A 0 = span of {evalWord A (List.ofFn σ) : σ : Fin 0 → Fin d}
  -- There is exactly one function Fin 0 → Fin d (the empty function),
  -- and evalWord of an empty list is 1.
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro M ⟨σ, rfl⟩
    have hempty : List.ofFn σ = ([] : List (Fin d)) := List.ofFn_eq_nil_iff.mpr rfl
    simp only [hempty, evalWord]
    exact Submodule.subset_span rfl
  · apply Submodule.span_le.mpr
    rintro M (rfl : M = 1)
    have := evalWord_mem_wordSpan A ([] : List (Fin d))
    simpa [evalWord] using this

/-- `rectSpan P A 0 = span{P}`: the level-0 rectangular span is just the 1-D subspace
spanned by `P` (since `wordSpan A 0 = span{1}`). -/
theorem rectSpan_zero_eq_span (P : Matrix (Fin D) (Fin D) ℂ) (A : MPSTensor d D) :
    rectSpan P A 0 = Submodule.span ℂ {P} := by
  simp only [rectSpan, wordSpan_zero_eq]
  rw [Submodule.map_span]
  congr 1
  ext M
  simp only [Set.mem_image, Set.mem_singleton_iff, LinearMap.mulLeft_apply]
  constructor
  · rintro ⟨N, rfl, rfl⟩; simp
  · intro hM; exact ⟨1, rfl, by simp [hM]⟩

/-- **Initial finrank**: when `P ≠ 0`, `rectSpan P A 0` has finrank 1. -/
theorem finrank_rectSpan_zero (P : Matrix (Fin D) (Fin D) ℂ)
    (A : MPSTensor d D) (hP : P ≠ 0) :
    finrank ℂ (rectSpan P A 0) = 1 := by
  rw [rectSpan_zero_eq_span]
  exact finrank_span_singleton hP

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

/-- **Tight pigeonhole**: there exists `n ≤ D * rank(P)` at which the monotone finrank
sequence for `rectSpan ((A i₀)^D) A n` has a consecutive equality.

This improves `exists_finrank_eq_succ_of_rectSpan` (which bounds by `D²`). -/
theorem exists_finrank_eq_succ_of_rectSpan_tight
    (A : MPSTensor d D) (i₀ : Fin d) :
    ∃ n ≤ D * ((A i₀) ^ D).rank,
      finrank ℂ (rectSpan ((A i₀) ^ D) A n) =
      finrank ℂ (rectSpan ((A i₀) ^ D) A (n + 1)) := by
  apply exists_consecutive_eq_of_monotone_bounded'
  · exact fun n => RectSpanGrowth.rectSpan_finrank_mono A i₀ n
  · exact fun n => rectSpan_finrank_le_rank_mul_D ((A i₀) ^ D) A n

/-- **Rank bound for powers**: `rank((A i₀)^D) ≤ D`. -/
theorem rank_pow_le (A : MPSTensor d D) (i₀ : Fin d) :
    ((A i₀) ^ D).rank ≤ D := by
  calc ((A i₀) ^ D).rank
      ≤ Fintype.card (Fin D) := Matrix.rank_le_card_width _
    _ = D := Fintype.card_fin D

/-! ### Part 3: Cumulative rectangular span transfer to cumulative span -/

/-- **Level-shift transfer**: `cumulativeRectSpan P A n ≤ cumulativeSpan A (m + n)` when
`P ∈ wordSpan A m`.

This is the cumulative analogue of `rectSpan_le_wordSpan`:
every element of `cumulativeRectSpan P A n` is a linear combination of `P · M_k`
where `M_k` is a word of length `≤ n`; since `P` is a word of length `m`,
the product `P · M_k` has length `m + k ≤ m + n`, putting it in `cumulativeSpan A (m + n)`. -/
theorem cumulativeRectSpan_le_cumulativeSpan
    (P : Matrix (Fin D) (Fin D) ℂ) (A : MPSTensor d D)
    {m : ℕ} (hP : P ∈ wordSpan A m) (n : ℕ) :
    cumulativeRectSpan P A n ≤ cumulativeSpan A (m + n) := by
  -- cumulativeRectSpan P A n = map(mulLeft P)(cumulativeSpan A n)
  -- Suffices: for each generator w with w.length ≤ n,
  -- P · evalWord A w ∈ cumulativeSpan A (m + n).
  rw [cumulativeRectSpan]
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro M ⟨w, hwlen, rfl⟩
  -- Need: evalWord A w ∈ comap (mulLeft P) (cumulativeSpan A (m + n))
  -- i.e., P * evalWord A w ∈ cumulativeSpan A (m + n)
  change (LinearMap.mulLeft ℂ P) (evalWord A w) ∈ cumulativeSpan A (m + n)
  simp only [LinearMap.mulLeft_apply]
  have hMmem : evalWord A w ∈ wordSpan A w.length := evalWord_mem_wordSpan A w
  have hProd : P * evalWord A w ∈ wordSpan A (m + w.length) :=
    wordSpan_mul_le A m w.length (Submodule.mul_mem_mul hP hMmem)
  exact wordSpan_le_cumulativeSpan A (by omega) hProd

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

/-! ### Part 4: Quantitative eigenvector rank-one in cumulativeSpan -/

/-- **Rank-one matrices from eigenvectors land in `cumulativeRectSpan`.**

If `φ ∈ range(toLin' P)`, then for every `ψ`, `vecMulVec φ ψ ∈ cumulativeRectSpan P A n`
whenever `cumulativeRectSpan P A n = range(mulLeft P)`.

This is the cumulative analogue of `vecMulVec_mem_rectSpan_of_mem_range_of_rectSpan_eq_range`. -/
theorem vecMulVec_mem_cumulativeRectSpan_of_mem_range
    (P : Matrix (Fin D) (Fin D) ℂ) (A : MPSTensor d D) {n : ℕ}
    {φ : Fin D → ℂ}
    (hφ : φ ∈ LinearMap.range (Matrix.toLin' P))
    (heq : cumulativeRectSpan P A n = LinearMap.range (LinearMap.mulLeft ℂ P)) :
    ∀ ψ : Fin D → ℂ, vecMulVec φ ψ ∈ cumulativeRectSpan P A n := by
  intro ψ
  rw [heq]
  exact vecMulVec_mem_range_mulLeft_of_mem_range_toLin P hφ ψ

/-- **Quantitative eigenvector rank-one in `cumulativeSpan`.**

Under `[NeZero D]`, `IsNormal A`, and `A i₀ *ᵥ φ = μ • φ` with `μ ≠ 0`:

  `∀ ψ, vecMulVec φ ψ ∈ cumulativeSpan A (D + D²)`

where the bound `D + D²` comes from:
- `D` for the power membership `(A i₀)^D ∈ wordSpan A D`
- `D²` for the cumulative span reaching ⊤ under `IsNormal`

This is the key quantitative intermediate result toward the paper's Lemma 2(b). -/
theorem vecMulVec_eigenvector_mem_cumulativeSpan [NeZero D]
    (A : MPSTensor d D) (i₀ : Fin d) (hN : IsNormal A)
    {φ : Fin D → ℂ} {μ : ℂ} (hμ : μ ≠ 0)
    (heig : A i₀ *ᵥ φ = μ • φ)
    (ψ : Fin D → ℂ) :
    vecMulVec φ ψ ∈ cumulativeSpan A (D + D ^ 2) := by
  set P := (A i₀) ^ D
  -- P ∈ wordSpan A D
  have hPmem : P ∈ wordSpan A D := pow_mem_wordSpan A i₀
  -- φ ∈ range(toLin' P)
  have hφ : φ ∈ LinearMap.range (toLin' P) := eigenvector_mem_range_toLin_pow A i₀ hμ heig
  -- cumulativeRectSpan P A (D²) = range(mulLeft P)
  have hcr : cumulativeRectSpan P A (D ^ 2) = LinearMap.range (LinearMap.mulLeft ℂ P) :=
    cumulativeRectSpan_eq_range_quantitative P A hN
  -- vecMulVec φ ψ ∈ cumulativeRectSpan P A (D²)
  have hmem : vecMulVec φ ψ ∈ cumulativeRectSpan P A (D ^ 2) :=
    vecMulVec_mem_cumulativeRectSpan_of_mem_range P A hφ hcr ψ
  -- Transfer: cumulativeRectSpan P A (D²) ≤ cumulativeSpan A (D + D²)
  exact cumulativeRectSpan_le_cumulativeSpan P A hPmem (D ^ 2) hmem

/-! ### Part 5: Tight ceiling for non-invertible case

When `A i₀` is not invertible, `rank((A i₀)^D) ≤ D - 1`, giving the ceiling
`D * (D-1) = D² - D` for the finrank of `range(mulLeft ((A i₀)^D))`.

This is the key numerical ingredient for the paper's Lemma 2(b) which gives
the bound `D² - D + 1` via `D + (D² - D - D + 1) = D² - D + 1`. -/

/-- `finrank(range(mulLeft ((A i₀)^D))) = D * rank((A i₀)^D)`, the exact ceiling. -/
theorem finrank_range_mulLeft_pow (A : MPSTensor d D) (i₀ : Fin d) :
    finrank ℂ (LinearMap.range (LinearMap.mulLeft ℂ ((A i₀) ^ D)))
      = D * ((A i₀) ^ D).rank :=
  finrank_range_mulLeft _

/-- `finrank(range(mulLeft ((A i₀)^D))) ≤ D²`, the coarse ceiling. -/
theorem finrank_range_mulLeft_pow_le_sq (A : MPSTensor d D) (i₀ : Fin d) :
    finrank ℂ (LinearMap.range (LinearMap.mulLeft ℂ ((A i₀) ^ D)))
      ≤ D ^ 2 := by
  rw [finrank_range_mulLeft_pow]
  calc D * ((A i₀) ^ D).rank
      ≤ D * D := Nat.mul_le_mul_left D (rank_pow_le A i₀)
    _ = D ^ 2 := by ring

/-! ### Part 6: Parametric assembly — toward exact Lemma 2(b)

The parametric assembly theorem combines:
1. Power membership: `(A i₀)^D ∈ wordSpan A D`
2. Eigenvector in range: `φ ∈ range(toLin' ((A i₀)^D))`
3. Stabilization: `rectSpan ((A i₀)^D) A n₀ = range(mulLeft ((A i₀)^D))`
4. Transfer: `vecMulVec φ ψ ∈ wordSpan A (D + n₀)`
5. Conditional assembly: `wordSpan A (D + n₀ + 2(D-1)) = ⊤`

into a single theorem parameterized by the stabilization witness `n₀`.

When the Wielandt inductive bound is available (giving `n₀ ≤ D² - 3D + 3`),
this yields `wordSpan A (D² - D + 1) = ⊤`.
-/

/-- **Parametric Lemma 2(b) assembly.**

Given the full eigenvector/row-eigenvector setup AND a stabilization witness `n₀`
such that `rectSpan ((A i₀)^D) A n₀ = range(mulLeft ((A i₀)^D))`, we get:

  `wordSpan A (D + n₀ + 2*(D-1)) = ⊤`

i.e., the word span at length `D + n₀ + 2D - 2` is the full matrix algebra.

### Proof strategy
1. Eigenvector `φ` lies in `range(toLin' ((A i₀)^D))` → for all `ψ`, `vecMulVec φ ψ ∈ rectSpan`
2. `rectSpan` stabilized at `n₀` → `vecMulVec φ ψ ∈ wordSpan A (D + n₀)`
3. Apply conditional assembly (eigenvector spreading + row spreading)
4. Output: `wordSpan A ((D-1) + ((D + n₀) + (D-1))) = ⊤`

This simplifies to `wordSpan A (3D + n₀ - 2) = ⊤`.

The hypothesis `n₀` is the key degree of freedom. Different bounds on `n₀`
give different final bounds:
- `n₀ = D² - 2D + 2` (normality witness): gives `D² + D = ⊤` (coarse)
- `n₀ = D² - 4D + 3` (from induction on D): gives `D² - D + 1 = ⊤` (sharp) -/
theorem wielandt_parametric_assembly [NeZero D]
    (A : MPSTensor d D)
    (hNormal : IsNormal (d := d) (D := D) A)
    -- Column eigenvector
    (i₀ : Fin d) (μ : ℂ) (hμ : μ ≠ 0)
    (φ : Fin D → ℂ) (hφ : φ ≠ 0)
    (heigφ : A i₀ *ᵥ φ = μ • φ)
    -- Row eigenvector (for the conditional assembly)
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
  -- Step 2: Apply conditional assembly
  exact wielandt_lemma2b_conditional A hNormal i₀ μ hμ φ hφ heigφ
    i₁ ν hν ψ₀ hψ₀ heigψ hRankOne

/-- **Corollary: the stabilization witness bounds the Wielandt length.**

If the rectSpan stabilizes at `n₀`, the word span reaches ⊤ at
level `3D + n₀ - 2` (when `D ≥ 1`). -/
theorem wielandt_length_from_stabilization [NeZero D]
    (A : MPSTensor d D) (hD : 1 ≤ D)
    (hNormal : IsNormal (d := d) (D := D) A)
    (i₀ : Fin d) (μ : ℂ) (hμ : μ ≠ 0)
    (φ : Fin D → ℂ) (hφ : φ ≠ 0)
    (heigφ : A i₀ *ᵥ φ = μ • φ)
    (i₁ : Fin d) (ν : ℂ) (hν : ν ≠ 0)
    (ψ₀ : Fin D → ℂ) (hψ₀ : ψ₀ ≠ 0)
    (heigψ : (A i₁)ᵀ *ᵥ ψ₀ = ν • ψ₀)
    {n₀ : ℕ}
    (hstab : rectSpan ((A i₀) ^ D) A n₀ =
             LinearMap.range (LinearMap.mulLeft ℂ ((A i₀) ^ D))) :
    wordSpan A (3 * D + n₀ - 2) = ⊤ := by
  have htop := wielandt_parametric_assembly A hNormal i₀ μ hμ φ hφ heigφ
    i₁ ν hν ψ₀ hψ₀ heigψ hstab
  have hlen : 3 * D + n₀ - 2 = (D - 1) + ((D + n₀) + (D - 1)) := by omega
  rwa [hlen]

end QuantitativeCeiling

end MPSTensor

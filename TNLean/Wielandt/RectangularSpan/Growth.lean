/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Kraus.Wielandt.RectangularSpan.Growth
import TNLean.Wielandt.RectangularSpan.Basic

/-!
# Rectangular span growth for matrix product tensors

The rectangular-span growth and stabilization results hold for arbitrary finite
matrix families. This module restates them for matrix product tensors.
-/

open scoped Matrix

namespace MPSTensor

open Module

variable {d D : ℕ}

namespace RectSpanGrowth

variable (A : MPSTensor d D) (i₀ : Fin d)

/-- Left multiplication by `A i₀` sends the rectangular span associated with
`(A i₀) ^ D` at length `n` into the span at length `n + 1`. -/
theorem mulLeft_mem_rectSpan_pow_succ
    (n : ℕ) {X : Matrix (Fin D) (Fin D) ℂ}
    (hX : X ∈ rectSpan ((A i₀) ^ D) A n) :
    (A i₀) * X ∈ rectSpan ((A i₀) ^ D) A (n + 1) :=
  Kraus.RectSpanGrowth.mulLeft_mem_rectSpan_pow_succ A i₀ n hX

/-- Left multiplication by `A i₀` as a linear map between consecutive
rectangular spans associated with `(A i₀) ^ D`. -/
noncomputable abbrev rectSpanLeftStep (n : ℕ) :
    (rectSpan ((A i₀) ^ D) A n) →ₗ[ℂ]
      (rectSpan ((A i₀) ^ D) A (n + 1)) :=
  Kraus.RectSpanGrowth.rectSpanLeftStep A i₀ n

/-- The left-step map is injective on every rectangular span associated with
`(A i₀) ^ D`. -/
theorem rectSpanLeftStep_injective (n : ℕ) :
    Function.Injective (rectSpanLeftStep A i₀ n) :=
  Kraus.RectSpanGrowth.rectSpanLeftStep_injective A i₀ n

/-- Finrank is non-decreasing along the rectangular spans associated with
`(A i₀) ^ D`. -/
theorem rectSpan_finrank_mono (n : ℕ) :
    finrank ℂ (rectSpan ((A i₀) ^ D) A n) ≤
      finrank ℂ (rectSpan ((A i₀) ^ D) A (n + 1)) :=
  Kraus.RectSpanGrowth.rectSpan_finrank_mono A i₀ n

/-- The left-step map is surjective when consecutive rectangular spans have the
same finrank. -/
theorem rectSpanLeftStep_surjective_of_finrank_eq (n : ℕ)
    (hfin : finrank ℂ (rectSpan ((A i₀) ^ D) A n) =
            finrank ℂ (rectSpan ((A i₀) ^ D) A (n + 1))) :
    Function.Surjective (rectSpanLeftStep A i₀ n) :=
  Kraus.RectSpanGrowth.rectSpanLeftStep_surjective_of_finrank_eq A i₀ n hfin

end RectSpanGrowth

/-- Every rectangular span is contained in the range of left multiplication by
its fixed matrix. -/
theorem rectSpan_le_range (P : Matrix (Fin D) (Fin D) ℂ)
    (A : MPSTensor d D) (n : ℕ) :
    rectSpan P A n ≤ LinearMap.range (LinearMap.mulLeft ℂ P) :=
  Kraus.rectSpan_le_range P A n

/-- If a fixed-length word span is the full matrix algebra, then every rectangular
span with that length is the full range of left multiplication. -/
theorem rectSpan_eq_range_of_wordSpan_eq_top
    (P : Matrix (Fin D) (Fin D) ℂ) (A : MPSTensor d D)
    {n : ℕ} (htop : wordSpan A n = ⊤) :
    rectSpan P A n = LinearMap.range (LinearMap.mulLeft ℂ P) :=
  Kraus.rectSpan_eq_range_of_wordSpan_eq_top P A htop

/-- Under normality, some rectangular span equals the full range of left
multiplication. -/
theorem exists_rectSpan_eq_range_of_isNormal
    (P : Matrix (Fin D) (Fin D) ℂ) (A : MPSTensor d D)
    (hN : IsNormal A) :
    ∃ n, rectSpan P A n = LinearMap.range (LinearMap.mulLeft ℂ P) := by
  obtain ⟨N₀, _hN₀pos, hN₀⟩ := hN
  exact ⟨N₀, Kraus.rectSpan_eq_range_of_wordSpan_eq_top P A
    ((wordSpan_eq_top_iff_isNBlkInjective A N₀).mpr hN₀)⟩

/-- A rectangular span equals the range of left multiplication when the two
submodules have the same finrank. -/
theorem rectSpan_eq_range_of_finrank_eq_range
    (P : Matrix (Fin D) (Fin D) ℂ) (A : MPSTensor d D) {n : ℕ}
    (hfin : finrank ℂ (rectSpan P A n) =
            finrank ℂ (LinearMap.range (LinearMap.mulLeft ℂ P))) :
    rectSpan P A n = LinearMap.range (LinearMap.mulLeft ℂ P) :=
  Kraus.rectSpan_eq_range_of_finrank_eq_range P A hfin

end MPSTensor

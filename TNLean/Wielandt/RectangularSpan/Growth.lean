/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.Wielandt.RectangularSpan.Growth
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

end RectSpanGrowth

/-- Under normality, some rectangular span equals the full range of left
multiplication. -/
theorem exists_rectSpan_eq_range_of_isNormal
    (P : Matrix (Fin D) (Fin D) ℂ) (A : MPSTensor d D)
    (hN : IsNormal A) :
    ∃ n, Kraus.rectSpan P A n = LinearMap.range (LinearMap.mulLeft ℂ P) := by
  obtain ⟨N₀, _hN₀pos, hN₀⟩ := hN
  exact ⟨N₀, Kraus.rectSpan_eq_range_of_wordSpan_eq_top P A
    ((wordSpan_eq_top_iff_isNBlkInjective A N₀).mpr hN₀)⟩

end MPSTensor

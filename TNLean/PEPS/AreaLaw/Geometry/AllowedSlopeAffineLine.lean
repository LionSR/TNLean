/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.Templates
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Allowed directions in affine spans

If the difference of two defining points has a horizontal, vertical or
one of the two diagonal slopes, every difference of points in their affine
span has an allowed slope. The defining points may coincide.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:initial-stars`, lines 352–359.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Differences of points in the affine span of an allowed pair have an allowed slope.
Auxiliary to Section 11, `geometry:initial-stars`, lines 352–359. -/
theorem isAllowedSlope_sub_of_mem_affineSpan_pair {p q v x : ℝ × ℝ}
    (hs : IsAllowedSlope (q - p)) (hv : v ∈ affineSpan ℝ {p, q})
    (hx : x ∈ affineSpan ℝ {p, q}) : IsAllowedSlope (x - v) := by
  obtain ⟨r, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hv
  obtain ⟨s, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hx
  simp only [AffineMap.lineMap_apply_module']
  dsimp [IsAllowedSlope] at hs ⊢
  rcases hs with hs | hs | hs | hs
  · left
    linear_combination (s - r) * hs
  · right; left
    linear_combination (s - r) * hs
  · right; right; left
    linear_combination (s - r) * hs
  · right; right; right
    linear_combination (s - r) * hs

end TNLean.PEPS.AreaLaw.Geometry

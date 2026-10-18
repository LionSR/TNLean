/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith

/-!
# The translated dyadic origin

The manuscript fixes the origin at (√2, √3). Its two coordinates, their sum,
and their difference lie strictly between consecutive integers. Consequently
the integer translates of the four prescribed supporting lines contain no
integer lattice point.

This is the arithmetic prerequisite for excluding lattice sites from geometric
edges. Identifying the supporting lines of the actual edges is a separate
geometric assertion.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, prop:two-families, lines 150–154 and 545–559.
Source revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The translated origin prescribed in the manuscript.
Source: area-law Section 11, prop:two-families, lines 150–154. -/
def dyadicOrigin : ℝ × ℝ := (Real.sqrt 2, Real.sqrt 3)

private theorem ne_int_of_between {x : ℝ} (n : ℤ)
    (hl : (n : ℝ) < x) (hu : x < (n : ℝ) + 1) (m : ℤ) : x ≠ (m : ℝ) := by
  intro h
  have hnm : n < m := Int.cast_lt.mp (h ▸ hl)
  have hmn : m < n + 1 := Int.cast_lt.mp (by
    simpa only [Int.cast_add, Int.cast_one] using h ▸ hu)
  exact (not_lt_of_ge (Int.add_one_le_iff.mpr hnm)) hmn

/-- Each coordinate of the origin, their sum, and their difference is
nonintegral. Source: area-law Section 11, prop:two-families, lines 150–154. -/
theorem dyadicOrigin_nonintegral (m : ℤ) :
    dyadicOrigin.1 ≠ (m : ℝ) ∧ dyadicOrigin.2 ≠ (m : ℝ) ∧
      dyadicOrigin.1 + dyadicOrigin.2 ≠ (m : ℝ) ∧
      dyadicOrigin.1 - dyadicOrigin.2 ≠ (m : ℝ) := by
  have h₂l : (4 / 3 : ℝ) < Real.sqrt 2 :=
    (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have h₃l : (5 / 3 : ℝ) < Real.sqrt 3 :=
    (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have h₂u : Real.sqrt 2 < 2 :=
    (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
  have h₃u : Real.sqrt 3 < 2 :=
    (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
  have h₂₃ : Real.sqrt 2 < Real.sqrt 3 :=
    Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  refine ⟨ne_int_of_between 1 ?_ ?_ m, ne_int_of_between 1 ?_ ?_ m,
    ne_int_of_between 3 ?_ ?_ m, ne_int_of_between (-1) ?_ ?_ m⟩ <;>
    norm_num [dyadicOrigin] <;> linarith

/-- No integer lattice point lies on an integer translate of any of the four
prescribed supporting lines. Source: area-law Section 11, prop:two-families,
lines 545–559. -/
theorem dyadicOrigin_supporting_lines_avoid_lattice (z : ℤ × ℤ) (m : ℤ) :
    (z.1 : ℝ) ≠ dyadicOrigin.1 + (m : ℝ) ∧
      (z.2 : ℝ) ≠ dyadicOrigin.2 + (m : ℝ) ∧
      (z.1 : ℝ) + (z.2 : ℝ) ≠ dyadicOrigin.1 + dyadicOrigin.2 + (m : ℝ) ∧
      (z.1 : ℝ) - (z.2 : ℝ) ≠ dyadicOrigin.1 - dyadicOrigin.2 + (m : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    apply (dyadicOrigin_nonintegral (z.1 - m)).1
    push_cast
    linarith
  · intro h
    apply (dyadicOrigin_nonintegral (z.2 - m)).2.1
    push_cast
    linarith
  · intro h
    apply (dyadicOrigin_nonintegral (z.1 + z.2 - m)).2.2.1
    push_cast
    linarith
  · intro h
    apply (dyadicOrigin_nonintegral (z.1 - z.2 - m)).2.2.2
    push_cast
    linarith

end TNLean.PEPS.AreaLaw.Geometry

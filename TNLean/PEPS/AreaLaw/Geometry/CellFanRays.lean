/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.CellFanCycle
import Mathlib.Analysis.Normed.Module.Ray

/-!
# Distinct directed rays of actual cell fans

Every actual fan endpoint is at the positive half-side distance from its center.
Two endpoint directions are on the same directed ray precisely when their slots
agree. Thus the rays defined by the actual endpoints are distinct, for every
optional midpoint subdivision. The statements do not require an initial-region
assignment or a choice of active boundaries.

## References

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `prop:two-families`, lines 299–323, and
`geometry:initial-stars`, lines 341–342 and 352–369.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Manuscript file:
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/`
`build/sections/10-geometry.tex`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The final endpoint has the actual fan half-side norm.
Source: Section 11, `prop:two-families`, lines 299–323, and
`geometry:initial-stars`, lines 341–342 and 352–363. -/
private theorem end_norm (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (s : CellFanSlot split) :
    ‖cellFanEnd o ℓ z split s - cellFanCenter o ℓ z‖ = (2 : ℝ) ^ ℓ / 2 := by
  exact norm_sub_cellFanCenter_of_mem_base o ℓ z split s
    (right_mem_segment ℝ _ _)

/-- Two actual endpoint directions coincide precisely when their slots agree.
Source: Section 11, `prop:two-families`, lines 299–323, and
`geometry:initial-stars`, lines 341–342 and 366–369. -/
theorem cellFanEnd_sameRay_iff (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (i j : CellFanSlot split) :
    SameRay ℝ
      (cellFanEnd o ℓ z split i - cellFanCenter o ℓ z)
      (cellFanEnd o ℓ z split j - cellFanCenter o ℓ z) ↔ i = j := by
  constructor
  · intro h
    exact (cellFanEnd_injective o ℓ z split) (by
      simpa only [sub_add_cancel] using congrArg
        (fun x : ℝ × ℝ ↦ x + cellFanCenter o ℓ z)
        (h.eq_of_norm_eq ((end_norm o ℓ z split i).trans
          (end_norm o ℓ z split j).symm)))
  · exact fun hij ↦ hij ▸ SameRay.rfl

/-- Actual fan endpoint directions are nonzero, including exponent zero.
Source: Section 11, `prop:two-families`, lines 299–323, and
`geometry:initial-stars`, lines 341–342 and 352–363. -/
private theorem end_ne_zero (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (s : CellFanSlot split) :
    cellFanEnd o ℓ z split s - cellFanCenter o ℓ z ≠ 0 := by
  exact norm_pos_iff.mp
    ((end_norm o ℓ z split s).symm ▸
      div_pos (pow_pos zero_lt_two ℓ) zero_lt_two)

/-- The actual directed ray from the center through a fan's final endpoint.
Source: Section 11, `prop:two-families`, lines 299–323, and
`geometry:initial-stars`, lines 341–342 and 366–369. -/
noncomputable def cellFanRay (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (s : CellFanSlot split) : Module.Ray ℝ (ℝ × ℝ) :=
  rayOfNeZero ℝ (cellFanEnd o ℓ z split s - cellFanCenter o ℓ z)
    (end_ne_zero o ℓ z split s)

/-- Distinct actual fan slots determine distinct directed rays.
Source: Section 11, `prop:two-families`, lines 299–323, and
`geometry:initial-stars`, lines 341–342 and 366–369. -/
theorem cellFanRay_injective (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) : Function.Injective (cellFanRay o ℓ z split) := by
  intro i j h
  exact (cellFanEnd_sameRay_iff o ℓ z split i j).mp
    ((ray_eq_iff (end_ne_zero o ℓ z split i)
      (end_ne_zero o ℓ z split j)).mp h)

end TNLean.PEPS.AreaLaw.Geometry

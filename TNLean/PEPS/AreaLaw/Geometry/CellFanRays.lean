/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.CellFanCycle
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Ray

/-!
# Directed rays and radial restrictions of actual cell fans

Every actual fan endpoint is at the positive half-side distance from its center.
Inside the closed square of that radius, its full directed ray agrees with the
radial segment from the center to the endpoint. This includes the center and
exponent zero, and uses only distance addition along a segment in the maximum norm.

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

/-- Within the endpoint radius, a directed ray agrees with its radial segment.
Auxiliary to OpenAI, Section 11, `geometry:initial-stars`, lines 352--370,
at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
private theorem mem_segment_iff_sameRay_of_dist_le
    {c e x : ℝ × ℝ} (hx : dist x c ≤ dist e c) :
    x ∈ segment ℝ c e ↔ SameRay ℝ (x - c) (e - c) := by
  constructor
  case mpr =>
    intro hray
    rcases wbtw_total_of_sameRay_vsub_left (R := ℝ) (x := c) (y := x) (z := e)
      hray with hbetween | hbeyond
    case inr =>
      have hdist := hbeyond.dist_add_dist
      rw [dist_comm c e, dist_comm c x] at hdist
      have hz : dist e x ≤ 0 := by linarith only [hx, hdist]
      have hxe : x = e := (dist_le_zero.mp hz).symm
      simpa only [hxe] using (right_mem_segment ℝ c e)
    case inl => exact hbetween.mem_segment
  case mp =>
    exact fun hxseg ↦ (mem_segment_iff_wbtw.mp hxseg).sameRay_vsub_left

/-- Within the closed square of the fan radius, a point lies on an endpoint
radial segment precisely when its displacement has the same directed ray as
that endpoint. The center is included, and exponent zero is permitted.
Source: OpenAI, Section 11, `geometry:initial-stars`, lines 333–370,
especially 352–370, and `prop:two-families`, lines 299–323, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem cellFan_mem_radial_iff_sameRay_of_mem_closedBall
    (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (s : CellFanSlot split) (x : ℝ × ℝ)
    (hx : x ∈ Metric.closedBall (cellFanCenter o ℓ z) ((2 : ℝ) ^ ℓ / 2)) :
    x ∈ segment ℝ (cellFanCenter o ℓ z) (cellFanEnd o ℓ z split s) ↔
      SameRay ℝ (x - cellFanCenter o ℓ z)
        (cellFanEnd o ℓ z split s - cellFanCenter o ℓ z) := by
  exact mem_segment_iff_sameRay_of_dist_le (by
    simpa only [dist_eq_norm,
      end_norm o ℓ z split s]
      using Metric.mem_closedBall.mp hx)

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

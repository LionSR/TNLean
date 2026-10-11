/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.FanRegularity
import TNLean.PEPS.AreaLaw.Geometry.CellFanSectors
import TNLean.PEPS.AreaLaw.Geometry.CellFanSlopes
import TNLean.PEPS.AreaLaw.Geometry.AllowedSlopeAffineLine
import TNLean.PEPS.AreaLaw.Geometry.FanRadialConvexity
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Nonempty connected pieces of a midpoint fan

In the plane with the maximum norm, take the eight elementary triangles
obtained by subdividing every side of a dyadic square at its midpoint.
After any selected family of actual radial segments is deleted, each
triangle remains nonempty and connected inside every positive-radius ball
about the center. The selected family may be empty; the center is then retained.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:initial-stars`, lines 352–370,
with the elementary fan of `prop:two-families`, lines 299–310.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Every positive-radius ball about the center meets an actual all-midpoint
fan triangle after any selected family of its actual radials is removed.

Auxiliary to OpenAI, *A two-dimensional area law from a global spectral gap*,
Section 11, `geometry:initial-stars`, lines 352–363, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The positive radius is derived when this statement is used in the initial geometry.
-/
theorem cellFanPolygon_sdiff_radials_inter_ball_nonempty
    (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (i : CellFanSlot (fun _ ↦ true))
    (A : Set (CellFanSlot (fun _ ↦ true))) (r : ℝ) (hr : 0 < r) :
    (((cellFanPolygon o ℓ z (fun _ ↦ true) i).region \
        (⋃ t ∈ A, segment ℝ (cellFanCenter o ℓ z)
          (cellFanEnd o ℓ z (fun _ ↦ true) t))) ∩
      Metric.ball (cellFanCenter o ℓ z) r).Nonempty := by
  have hregular :=
    (cellFanPolygon_interior_nonempty_and_closure_eq o ℓ z (fun _ ↦ true) i).2
  have hc : cellFanCenter o ℓ z ∈
      (cellFanPolygon o ℓ z (fun _ ↦ true) i).region :=
    subset_convexHull ℝ
      ({cellFanCenter o ℓ z, cellFanStart o ℓ z (fun _ ↦ true) i,
        cellFanEnd o ℓ z (fun _ ↦ true) i} : Set (ℝ × ℝ)) (Or.inl rfl)
  obtain ⟨x, hx, hxr⟩ :=
    Metric.mem_closure_iff.mp
      (show cellFanCenter o ℓ z ∈
          closure (interior (cellFanPolygon o ℓ z (fun _ ↦ true) i).region)
        from hregular.symm ▸ hc) r hr
  refine ⟨x, ⟨interior_subset hx, ?_⟩, Metric.mem_ball'.mpr hxr⟩
  intro hxradial
  obtain ⟨t, _, hxt⟩ := Set.mem_iUnion₂.mp hxradial
  apply cellFanPolygon_interior_not_isAllowedSlope_sub_center o ℓ z i hx
  have hs :=
    (cellFanPolygon_base_and_radial_isAllowedSlope o ℓ z (fun _ ↦ true) t).2
  exact isAllowedSlope_sub_of_mem_affineSpan_pair hs
    (right_mem_affineSpan_pair ℝ
      (cellFanEnd o ℓ z (fun _ ↦ true) t) (cellFanCenter o ℓ z))
    ((convexHull_subset_affineSpan (𝕜 := ℝ)
      {cellFanEnd o ℓ z (fun _ ↦ true) t, cellFanCenter o ℓ z})
      (segment_subset_convexHull (𝕜 := ℝ)
        (s := {cellFanEnd o ℓ z (fun _ ↦ true) t, cellFanCenter o ℓ z})
        (Or.inr rfl) (Or.inl rfl) hxt))

/-- Every actual midpoint-fan triangle remains connected inside a positive-radius
ball about its center after any selected family of actual radials is removed.
Auxiliary to OpenAI, *A two-dimensional area law from a global spectral gap*,
Section 11, `geometry:initial-stars`, lines 352–370, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/
theorem cellFanPolygon_sdiff_radials_inter_ball_isConnected
    (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (i : CellFanSlot (fun _ ↦ true))
    (A : Set (CellFanSlot (fun _ ↦ true))) (r : ℝ) (hr : 0 < r) :
    IsConnected (((cellFanPolygon o ℓ z (fun _ ↦ true) i).region \
        (⋃ t ∈ A, segment ℝ (cellFanCenter o ℓ z)
          (cellFanEnd o ℓ z (fun _ ↦ true) t))) ∩
      Metric.ball (cellFanCenter o ℓ z) r) := by
  exact
    ((cellFanPolygon_sdiff_radials_convex o ℓ z (fun _ ↦ true) i A).inter
      (convex_ball (cellFanCenter o ℓ z) r)).isConnected
      (cellFanPolygon_sdiff_radials_inter_ball_nonempty o ℓ z i A r hr)

end TNLean.PEPS.AreaLaw.Geometry

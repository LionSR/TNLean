/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# Clipping a unit segment by a ball

A closed ball of radius `η ∈ [0, 1]` about the initial endpoint of a unit
segment cuts out the segment ending at affine parameter `η`. This includes
both radius zero and radius one.

## References

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:repair-induction`, lines 501–511.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Manuscript file:
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/`
`build/sections/10-geometry.tex`.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Clipping a unit segment at its initial endpoint.
Auxiliary to area-law Section 11, `geometry:repair-induction`, lines 501–511. -/
theorem segment_inter_closedBall_of_dist_eq_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : E) (hab : dist a b = 1)
    {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    segment ℝ a b ∩ Metric.closedBall a η =
      segment ℝ a (AffineMap.lineMap a b η) := by
  rw [segment_eq_image_lineMap ℝ a b, ← Set.image_inter_preimage]
  have himage : (AffineMap.lineMap a b) '' Set.Icc 0 η =
      segment ℝ a ((AffineMap.lineMap a b) η) := by
    simpa only [segment_eq_Icc hη0, AffineMap.lineMap_apply_zero] using
      image_segment ℝ (AffineMap.lineMap a b) (0 : ℝ) η
  refine (congrArg (Set.image (AffineMap.lineMap a b)) ?_).trans himage
  simp only [Set.ext_iff, Set.mem_inter_iff, Set.mem_Icc, Set.mem_preimage,
    Metric.mem_closedBall, dist_lineMap_left, hab, mul_one,
    Real.norm_eq_abs, abs_le]
  grind

end TNLean.PEPS.AreaLaw.Geometry

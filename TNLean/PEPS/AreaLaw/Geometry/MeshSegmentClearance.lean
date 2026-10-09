/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.MeshGeometry
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Normed.Affine.Convex

/-!
# Clearance from allowed-slope mesh segments

In the sup norm, a point of a translated mesh outside a segment with mesh
endpoints is at least half a mesh spacing from that segment when its slope is
horizontal, vertical or diagonal. This also holds when the point lies on the
supporting line: an endpoint between the point and the segment gives the stronger
full-spacing bound.
Coincident endpoints are permitted.

## References

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
Section 11, `geometry:initial-stars`, lines 352–359, and
`geometry:repair-induction`, lines 501–511.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Manuscript file:
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/`
`build/sections/10-geometry.tex`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- A mesh point outside an allowed-slope mesh segment is at least half a mesh
spacing from every point of that segment, including when its supporting line
contains the mesh point.
Auxiliary to Section 11, `geometry:initial-stars`, lines 352–359, and
`geometry:repair-induction`, lines 501–511. -/
theorem affineMesh_segment_dist_ge_of_not_mem
    {o : ℝ × ℝ} {q : ℝ} (hq : 0 < q)
    {a b p x : ℝ × ℝ}
    (ha : a ∈ affineMesh o q) (hb : b ∈ affineMesh o q)
    (hp : p ∈ affineMesh o q)
    (hs : IsAllowedSlope (b - a))
    (hout : p ∉ segment ℝ a b)
    (hx : x ∈ segment ℝ a b) :
    q / 2 ≤ dist p x := by
  by_cases hline : p ∈ affineSpan ℝ ({a, b} : Set (ℝ × ℝ))
  · have hcol : Collinear ℝ ({p, a, b} : Set (ℝ × ℝ)) :=
      collinear_insert_of_mem_affineSpan_pair hline
    rcases hcol.wbtw_or_wbtw_or_wbtw with hpa | hab | hbp
    · have hpax : Wbtw ℝ p a x :=
        hpa.trans_right_left (mem_segment_iff_wbtw.mp hx)
      have hpa_ne : p ≠ a :=
        (ne_of_mem_of_not_mem (left_mem_segment ℝ a b) hout).symm
      have hdist : q ≤ dist p a := affineMesh_dist_ge hq hp ha hpa_ne
      have hadd := hpax.dist_add_dist
      linarith [dist_nonneg (x := a) (y := x)]
    · have hpbx : Wbtw ℝ p b x :=
        hab.symm.trans_right_left (mem_segment_iff_wbtw.mp hx).symm
      have hpb_ne : p ≠ b :=
        (ne_of_mem_of_not_mem (right_mem_segment ℝ a b) hout).symm
      have hdist : q ≤ dist p b := affineMesh_dist_ge hq hp hb hpb_ne
      have hadd := hpbx.dist_add_dist
      linarith [dist_nonneg (x := b) (y := x)]
    · exact (hout (mem_segment_iff_wbtw.mpr hbp.symm)).elim
  · have hxline : x ∈ affineSpan ℝ ({a, b} : Set (ℝ × ℝ)) :=
      (mem_segment_iff_wbtw.mp hx).mem_affineSpan
    exact affineMesh_line_dist_ge hq ha hb hp hs hline hxline

end TNLean.PEPS.AreaLaw.Geometry

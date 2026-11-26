/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.BirthRegions.Layers.BeltMarks
import QICLean.ManyBody.Sites.Template.Defs
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Normed.Affine.Convex
import TNLean.PEPS.AreaLaw.BirthRegions.Layers.LocalLayers
import QICLean.ManyBody.Sites.Dyadic.DistanceLayers
import TNLean.PEPS.AreaLaw.BirthRegions.Layers.AdjacentScales
import QICLean.ManyBody.Sites.Dyadic.LayerPartition

/-!
# Separation on the quarter mesh

The nine marks of every cell at scale `j` lie on the mesh of spacing
`2 ^ ℓ / 4` whenever `ℓ ≤ j + 1`. Distinct mesh points are separated by
one mesh spacing. A mesh point outside a line of horizontal, vertical or
diagonal slope through mesh points is separated from that line by at
least half a mesh spacing, in the maximum metric on the plane.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:initial-stars`, lines 352–359.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.

## Clearance from allowed-slope mesh segments

In the sup norm, a point of a translated mesh outside a segment with mesh
endpoints is at least half a mesh spacing from that segment when its slope is
horizontal, vertical or diagonal. This also holds when the point lies on the
supporting line: an endpoint between the point and the segment gives the stronger
full-spacing bound.
Coincident endpoints are permitted.

### References

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
Section 11, `geometry:initial-stars`, lines 352–359, and
`geometry:repair-induction`, lines 501–511.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Manuscript file:
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/`
`build/sections/10-geometry.tex`.
Independently proved from the manuscript; no upstream Lean proof text is reused.

It also contains the following results.

* `TNLean.PEPS.AreaLaw.Geometry.fineLayer_marks_dist_ge`: separation of actual fine-layer marks.
* `TNLean.PEPS.AreaLaw.Geometry.fineLayer_near_mark_quarter_mesh`,
  `TNLean.PEPS.AreaLaw.Geometry.dyadicNeighborhood_dist_later_layer_fineScale`: actual layers and
  meshes near a fine-cell mark.
-/

open ManyBody (IsAllowedSlope dyadicCell dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices
  dyadicLayer dyadicLayer_dist_lower dyadicNeighborhood dyadicNeighborhood_exists_dist_le
  fineLayerIndices integerPoint)

section MeshGeometry

section

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The translated square mesh with spacing `q`.
Source: area-law Section 11, `geometry:initial-stars`, lines 352–359. -/
def affineMesh (o : ℝ × ℝ) (q : ℝ) : Set (ℝ × ℝ) :=
  Set.range (fun z : ℤ × ℤ ↦ o + q • integerPoint z)

/-- The cell marks lie on the quarter mesh whenever their scale is at least `ℓ - 1`.
Source: area-law Section 11, `geometry:initial-stars`, lines 352–359. -/
theorem beltMarks_subset_affineMesh (o : ℝ × ℝ) (ℓ j : ℕ)
    (F : Finset (ℤ × ℤ)) (hℓj : ℓ ≤ j + 1) :
    (beltMarks o j F : Set (ℝ × ℝ)) ⊆ affineMesh o ((2 : ℝ) ^ ℓ / 4) := by
  classical
  intro x hx
  obtain ⟨z, _, hz⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
  have hp : ((2 : ℝ) ^ ℓ / 4) * (2 : ℝ) ^ (j + 1 - ℓ) = (2 : ℝ) ^ j / 2 := by
    rw [div_mul_eq_mul_div, ← pow_add, Nat.add_sub_of_le hℓj, pow_succ]
    ring
  refine ⟨((2 : ℤ) ^ (j + 1 - ℓ) * (2 * z.1 + i.1.val),
    (2 : ℤ) ^ (j + 1 - ℓ) * (2 * z.2 + i.2.val)), ?_⟩
  apply Prod.ext <;> dsimp [integerPoint] <;> push_cast <;>
    rw [← mul_assoc, hp] <;> ring

private theorem abs_mul_int_ge {q : ℝ} (hq : 0 < q) (n : ℤ) (hn : n ≠ 0) :
    q ≤ |q * (n : ℝ)| := by
  have hn' : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
  simpa [abs_mul, abs_of_pos hq] using mul_le_mul_of_nonneg_left hn' hq.le

/-- Distinct points of a positive-spacing mesh are separated by at least its spacing.
Source: area-law Section 11, `geometry:initial-stars`, lines 352–359. -/
theorem affineMesh_dist_ge {o : ℝ × ℝ} {q : ℝ} (hq : 0 < q)
    {x y : ℝ × ℝ} (hx : x ∈ affineMesh o q) (hy : y ∈ affineMesh o q)
    (hxy : x ≠ y) : q ≤ dist x y := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have hab : a ≠ b := by rintro rfl; exact hxy rfl
  have hab' : a.1 ≠ b.1 ∨ a.2 ≠ b.2 := by
    by_contra h
    push Not at h
    exact hab (Prod.ext h.1 h.2)
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  rcases hab' with h | h
  · have hg := abs_mul_int_ge hq (a.1 - b.1) (sub_ne_zero.mpr h)
    have he : (o + q • integerPoint a).1 - (o + q • integerPoint b).1 =
        q * ((a.1 - b.1 : ℤ) : ℝ) := by dsimp [integerPoint]; push_cast; ring
    exact (he ▸ hg).trans (le_max_left _ _)
  · have hg := abs_mul_int_ge hq (a.2 - b.2) (sub_ne_zero.mpr h)
    have he : (o + q • integerPoint a).2 - (o + q • integerPoint b).2 =
        q * ((a.2 - b.2 : ℤ) : ℝ) := by dsimp [integerPoint]; push_cast; ring
    exact (he ▸ hg).trans (le_max_right _ _)

private theorem mem_nonvertical_line_iff {u v x : ℝ × ℝ} {m : ℝ}
    (huv : u.1 ≠ v.1) (hs : v.2 - u.2 = m * (v.1 - u.1)) :
    x ∈ affineSpan ℝ {u, v} ↔ x.2 - m * x.1 = u.2 - m * u.1 := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  constructor
  · rintro ⟨r, rfl⟩
    rw [AffineMap.lineMap_apply_module']
    dsimp
    linear_combination r * hs
  · intro hx
    refine ⟨(x.1 - u.1) / (v.1 - u.1), ?_⟩
    have hd := div_mul_cancel₀ (x.1 - u.1) (sub_ne_zero.mpr huv.symm)
    rw [AffineMap.lineMap_apply_module']
    apply Prod.ext <;> dsimp
    · linarith
    · linear_combination ((x.1 - u.1) / (v.1 - u.1)) * hs + m * hd - hx

private theorem mem_vertical_line_iff {u v x : ℝ × ℝ}
    (huv : u.2 ≠ v.2) (hs : u.1 = v.1) :
    x ∈ affineSpan ℝ {u, v} ↔ x.1 = u.1 := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  constructor
  · rintro ⟨r, rfl⟩
    rw [AffineMap.lineMap_apply_module']
    dsimp
    rw [← hs]
    ring
  · intro hx
    refine ⟨(x.2 - u.2) / (v.2 - u.2), ?_⟩
    have hd := div_mul_cancel₀ (x.2 - u.2) (sub_ne_zero.mpr huv.symm)
    rw [AffineMap.lineMap_apply_module']
    apply Prod.ext <;> dsimp
    · rw [← hs, hx]; ring
    · linarith

private theorem mesh_linear_gap {o : ℝ × ℝ} {q : ℝ} (hq : 0 < q)
    (a b : ℤ) {x u : ℝ × ℝ} (hx : x ∈ affineMesh o q) (hu : u ∈ affineMesh o q)
    (hne : (a : ℝ) * x.1 + b * x.2 ≠ (a : ℝ) * u.1 + b * u.2) :
    q ≤ |((a : ℝ) * x.1 + b * x.2) - ((a : ℝ) * u.1 + b * u.2)| := by
  obtain ⟨c, rfl⟩ := hx
  obtain ⟨d, rfl⟩ := hu
  have he : ((a : ℝ) * (o + q • integerPoint c).1 +
      b * (o + q • integerPoint c).2) -
      ((a : ℝ) * (o + q • integerPoint d).1 + b * (o + q • integerPoint d).2) =
      q * ((a * (c.1 - d.1) + b * (c.2 - d.2) : ℤ) : ℝ) := by
    dsimp [integerPoint]
    push_cast
    ring
  have hn : a * (c.1 - d.1) + b * (c.2 - d.2) ≠ 0 := by
    intro hn
    apply hne
    apply sub_eq_zero.mp
    rw [he, hn]
    simp
  rw [he]
  exact abs_mul_int_ge hq _ hn

private theorem linear_form_dist_le (x y : ℝ × ℝ) {m : ℝ} (hm : |m| ≤ 1) :
    |(x.2 - m * x.1) - (y.2 - m * y.1)| ≤ 2 * dist x y := by
  have hfst : |x.1 - y.1| ≤ dist x y := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact le_max_left _ _
  have hsnd : |x.2 - y.2| ≤ dist x y := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact le_max_right _ _
  calc
    _ = |(x.2 - y.2) - m * (x.1 - y.1)| := by congr 1; ring
    _ ≤ |x.2 - y.2| + |m * (x.1 - y.1)| := abs_sub _ _
    _ = |x.2 - y.2| + |m| * |x.1 - y.1| := by rw [abs_mul]
    _ ≤ dist x y + |x.1 - y.1| := by
      exact add_le_add hsnd (by simpa using mul_le_mul_of_nonneg_right hm (abs_nonneg _))
    _ ≤ dist x y + dist x y := add_le_add le_rfl hfst
    _ = 2 * dist x y := by ring

private theorem nonvertical_mesh_line_dist_ge {o : ℝ × ℝ} {q : ℝ}
    (hq : 0 < q) {u v x y : ℝ × ℝ} (hu : u ∈ affineMesh o q)
    (hx : x ∈ affineMesh o q) (m : ℤ) (hm : |(m : ℝ)| ≤ 1)
    (huv : u.1 ≠ v.1) (hs : v.2 - u.2 = (m : ℝ) * (v.1 - u.1))
    (hout : x ∉ affineSpan ℝ {u, v}) (hy : y ∈ affineSpan ℝ {u, v}) :
    q / 2 ≤ dist x y := by
  have hne : x.2 - (m : ℝ) * x.1 ≠ u.2 - (m : ℝ) * u.1 := by
    intro he
    exact hout ((mem_nonvertical_line_iff huv hs).mpr he)
  have hne' : ((-m : ℤ) : ℝ) * x.1 + (1 : ℤ) * x.2 ≠
      ((-m : ℤ) : ℝ) * u.1 + (1 : ℤ) * u.2 := by
    simpa [sub_eq_add_neg, add_comm] using hne
  have hg := mesh_linear_gap hq (-m) 1 hx hu hne'
  have hg' : q ≤ |(x.2 - (m : ℝ) * x.1) - (u.2 - (m : ℝ) * u.1)| := by
    simpa [sub_eq_add_neg, add_comm] using hg
  have hy' := (mem_nonvertical_line_iff huv hs).mp hy
  rw [← hy'] at hg'
  have hb := linear_form_dist_le x y hm
  linarith

/-- A mesh point outside a line of an allowed slope through mesh points is at least
half a mesh spacing from every point of the line.
Source: area-law Section 11, `geometry:initial-stars`, lines 352–359. -/
theorem affineMesh_line_dist_ge {o : ℝ × ℝ} {q : ℝ} (hq : 0 < q)
    {u v x y : ℝ × ℝ} (hu : u ∈ affineMesh o q) (hv : v ∈ affineMesh o q)
    (hx : x ∈ affineMesh o q) (hs : IsAllowedSlope (v - u))
    (hout : x ∉ affineSpan ℝ {u, v}) (hy : y ∈ affineSpan ℝ {u, v}) :
    q / 2 ≤ dist x y := by
  by_cases huv : u = v
  · subst v
    have hy' : y = u := by simpa using hy
    subst y
    have hxu : x ≠ u := by
      intro h
      subst x
      exact hout (left_mem_affineSpan_pair ℝ u u)
    have hg := affineMesh_dist_ge hq hx hv hxu
    linarith
  by_cases hf : u.1 = v.1
  · have hsnd : u.2 ≠ v.2 := by
      intro h
      exact huv (Prod.ext hf h)
    have hne : x.1 ≠ u.1 := by
      intro h
      exact hout ((mem_vertical_line_iff hsnd hf).mpr h)
    have hg := mesh_linear_gap hq 1 0 hx hu (by simpa using hne)
    have hg' : q ≤ |x.1 - u.1| := by simpa using hg
    have hy' := (mem_vertical_line_iff hsnd hf).mp hy
    rw [← hy'] at hg'
    have hb : |x.1 - y.1| ≤ dist x y := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      exact le_max_left _ _
    linarith
  rcases hs with hs | hs | hs | hs
  · exact False.elim (hf (by dsimp at hs; linarith))
  · exact nonvertical_mesh_line_dist_ge hq hu hx 0 (by norm_num) hf
      (by dsimp at hs; norm_num; linarith) hout hy
  · exact nonvertical_mesh_line_dist_ge hq hu hx 1 (by norm_num) hf
      (by dsimp at hs; norm_num; linarith) hout hy
  · exact nonvertical_mesh_line_dist_ge hq hu hx (-1) (by norm_num) hf
      (by dsimp at hs; norm_num; linarith) hout hy

end TNLean.PEPS.AreaLaw.Geometry
end

end

section

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

end

end MeshGeometry

namespace TNLean.PEPS.AreaLaw.Geometry

section FineMarkSeparation

/-!
## Separation of actual fine-layer marks

At sufficiently late layers, distinct fine-cell marks are separated by at least
one quarter of the larger incident cell side. The proof combines the separation
of nonadjacent closed layers with the quarter mesh of marks in adjacent layers.
It applies to every actual fine-layer cell, hence in particular to selected belt
cells, and includes marks on cell boundaries.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:initial-stars`, lines 325–339 and
352–359. This proves the point-separation assertion, without a fan or ray
construction.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

private theorem cellMark_mem_closed_layer (o : ℝ × ℝ) (k : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (z : ℤ × ℤ) (x : ℝ × ℝ)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (hx : x ∈ beltCellMarks o (fineScaleIndex k) z) :
    x ∈ closure (dyadicLayer o k Z C) := by
  have hcell := dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices
    o k (fineScaleIndex k) Z C z (fineScaleIndex_le k) hz
  exact closure_mono hcell
    (beltCellMarks_subset_closure_dyadicCell o (fineScaleIndex k) z hx)

private theorem cellMark_mem_quarter_mesh (o : ℝ × ℝ) (ℓ j : ℕ)
    (z : ℤ × ℤ) (x : ℝ × ℝ) (hℓj : ℓ ≤ j + 1)
    (hx : x ∈ beltCellMarks o j z) : x ∈ affineMesh o ((2 : ℝ) ^ ℓ / 4) := by
  classical
  apply beltMarks_subset_affineMesh o ℓ j {z} hℓj
  exact Finset.mem_biUnion.mpr ⟨z, by simp, hx⟩

private theorem fineLayer_marks_dist_ge_left (o : ℝ × ℝ) (k h : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (z w : ℤ × ℤ) (x y : ℝ × ℝ)
    (hC : 2 ≤ C) (hk : 50000000 ≤ k)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (hw : w ∈ fineLayerIndices o h (fineScaleIndex h) Z C)
    (hx : x ∈ beltCellMarks o (fineScaleIndex k) z)
    (hy : y ∈ beltCellMarks o (fineScaleIndex h) w) (hne : x ≠ y) :
    (2 : ℝ) ^ fineScaleIndex k / 4 ≤ dist x y := by
  by_contra! hdist
  have ht : 0 < (2 : ℝ) ^ fineScaleIndex k := by positivity
  have hnear : dist x y < 10 * (2 : ℝ) ^ fineScaleIndex k := by linarith
  have hkh := (dyadicLayer_nearby_indices o k h Z C x y hC hk
    (cellMark_mem_closed_layer o k Z C z x hz hx)
    (cellMark_mem_closed_layer o h Z C w y hw hy) hnear).2
  have hmono := fineScaleIndex_mono hkh
  have hstep := fineScaleIndex_succ h
  have hscale : fineScaleIndex k ≤ fineScaleIndex h + 1 := by omega
  have hxmesh := cellMark_mem_quarter_mesh o (fineScaleIndex k) (fineScaleIndex k)
    z x (by omega) hx
  have hymesh := cellMark_mem_quarter_mesh o (fineScaleIndex k) (fineScaleIndex h)
    w y hscale hy
  have hsep := affineMesh_dist_ge (by positivity) hxmesh hymesh hne
  linarith

/-- Actual fine-layer marks are separated by one quarter of the larger incident side.
Source: area-law Section 11, `geometry:initial-stars`, lines 325–339 and 352–359. -/
theorem fineLayer_marks_dist_ge (o : ℝ × ℝ) (k h : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (z w : ℤ × ℤ) (x y : ℝ × ℝ)
    (hC : 2 ≤ C) (hk : 50000000 ≤ k) (hh : 50000000 ≤ h)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (hw : w ∈ fineLayerIndices o h (fineScaleIndex h) Z C)
    (hx : x ∈ beltCellMarks o (fineScaleIndex k) z)
    (hy : y ∈ beltCellMarks o (fineScaleIndex h) w) (hne : x ≠ y) :
    max ((2 : ℝ) ^ fineScaleIndex k) ((2 : ℝ) ^ fineScaleIndex h) / 4 ≤ dist x y := by
  have hksep := fineLayer_marks_dist_ge_left o k h Z C z w x y hC hk hz hw hx hy hne
  have hhsep := fineLayer_marks_dist_ge_left o h k Z C w z y x hC hh hw hz hy hx hne.symm
  rw [dist_comm] at hhsep
  have hm : max ((2 : ℝ) ^ fineScaleIndex k) ((2 : ℝ) ^ fineScaleIndex h) ≤
      4 * dist x y := max_le (by linarith) (by linarith)
  linarith

end FineMarkSeparation

section NearMarkGeometry

/-!
## Actual layers and meshes near a fine-cell mark

A closed neighborhood of radius ten fine-cell sides around an actual cell
mark meets only its own or an adjacent layer. All marks of a cell meeting
that neighborhood lie on one common quarter mesh. The closed radius is
handled by the sixteen-side separation of nonadjacent layers.

The initial dummy neighborhood is also separated from every later layer by
at least sixteen of that layer's fine sides. The reference layer alone has
the explicit late bound. The origin and endpoint set are arbitrary; neither
selected belt membership nor a supplied local geometric description is needed.
Active rays and sectors remain separate assertions.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:initial-stars`, lines 352–359;
`geometry:layer-distance`, lines 179–191; and scale comparison, lines 200–207.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

/-- The marks of one cell inherit the existing quarter-mesh inclusion.
Auxiliary to Section 11, `geometry:initial-stars`, lines 352–359. -/
private theorem cellMarks_subset_quarter_mesh (o : ℝ × ℝ) (ℓ j : ℕ)
    (z : ℤ × ℤ) (hℓj : ℓ ≤ j + 1) :
    (beltCellMarks o j z : Set (ℝ × ℝ)) ⊆ affineMesh o ((2 : ℝ) ^ ℓ / 4) := by
  classical
  simpa only [beltMarks, Finset.singleton_biUnion] using
    beltMarks_subset_affineMesh o ℓ j {z} hℓj

/-- An actual fine cell meeting the closed ten-side neighborhood of an actual
cell mark lies in a neighboring layer and shares its quarter mesh.
Source: Section 11, `geometry:initial-stars`, lines 352–359. -/
theorem fineLayer_near_mark_quarter_mesh
    (o : ℝ × ℝ) (k h : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (z w : ℤ × ℤ) (v : ℝ × ℝ)
    (hC : 2 ≤ C) (hk : 50000000 ≤ k)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (hw : w ∈ fineLayerIndices o h (fineScaleIndex h) Z C)
    (hv : v ∈ beltCellMarks o (fineScaleIndex k) z)
    (hcontact : (closure (dyadicCell o (fineScaleIndex h) w) ∩
      Metric.closedBall v (10 * (2 : ℝ) ^ fineScaleIndex k)).Nonempty) :
    (h ≤ k + 1 ∧ k ≤ h + 1) ∧
    (fineScaleIndex h = fineScaleIndex k ∨
      fineScaleIndex h + 1 = fineScaleIndex k ∨
      fineScaleIndex h = fineScaleIndex k + 1) ∧
    ((beltCellMarks o (fineScaleIndex k) z : Set (ℝ × ℝ)) ∪
      (beltCellMarks o (fineScaleIndex h) w : Set (ℝ × ℝ))) ⊆
      affineMesh o ((2 : ℝ) ^ fineScaleIndex k / 4) := by
  obtain ⟨y, hycell, hyball⟩ := hcontact
  have hvD : v ∈ closure (dyadicLayer o k Z C) :=
    closure_mono (dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices o k
      (fineScaleIndex k) Z C z (fineScaleIndex_le k) hz)
      (beltCellMarks_subset_closure_dyadicCell o (fineScaleIndex k) z hv)
  have hyD : y ∈ closure (dyadicLayer o h Z C) :=
    closure_mono (dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices o h
      (fineScaleIndex h) Z C w (fineScaleIndex_le h) hw) hycell
  have hdist : dist v y ≤ 10 * (2 : ℝ) ^ fineScaleIndex k :=
    Metric.mem_closedBall'.mp hyball
  have hnot : ¬ (k + 2 ≤ h ∨ h + 2 ≤ k) := by
    intro hnon
    have hsep := dyadicLayer_dist_nonadjacent_fineScale o k h Z C v y hC hk
      hnon hvD hyD
    have ht : 0 < (2 : ℝ) ^ fineScaleIndex k := pow_pos zero_lt_two _
    linarith
  have hadj : h ≤ k + 1 ∧ k ≤ h + 1 := by omega
  have hlo := fineScaleIndex_mono hadj.2
  have hhi := fineScaleIndex_mono hadj.1
  have hstepk := fineScaleIndex_succ k
  have hsteph := fineScaleIndex_succ h
  have hindices : fineScaleIndex k ≤ fineScaleIndex h + 1 ∧
      fineScaleIndex h ≤ fineScaleIndex k + 1 := by omega
  have hcases : fineScaleIndex h = fineScaleIndex k ∨
      fineScaleIndex h + 1 = fineScaleIndex k ∨
      fineScaleIndex h = fineScaleIndex k + 1 := by omega
  refine ⟨hadj, hcases, ?_⟩
  exact Set.union_subset
    (cellMarks_subset_quarter_mesh o (fineScaleIndex k) (fineScaleIndex k) z (by omega))
    (cellMarks_subset_quarter_mesh o (fineScaleIndex k) (fineScaleIndex h) w hindices.1)

/-- The closed dummy neighborhood is separated from a later closed layer
by sixteen of that layer's fine sides.
Source: Section 11, `geometry:initial-stars`, lines 352–359;
`geometry:layer-distance`, lines 179–191; and scale comparison, lines 200–207. -/
theorem dyadicNeighborhood_dist_later_layer_fineScale
    (o : ℝ × ℝ) (k₀ k : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (x y : ℝ × ℝ) (hC : 2 ≤ C) (hk : 50000000 ≤ k)
    (hkk : k₀ + 1 ≤ k)
    (hx : x ∈ closure (dyadicNeighborhood o k₀ Z C))
    (hy : y ∈ closure (dyadicLayer o k Z C)) :
    16 * (2 : ℝ) ^ fineScaleIndex k ≤ dist x y := by
  obtain ⟨u, hu, hxu⟩ := dyadicNeighborhood_exists_dist_le o k₀ Z C x hx
  have hyu := dyadicLayer_dist_lower o k Z C y hy u hu
  have htriangle : dist y (integerPoint u) ≤ dist x y + dist x (integerPoint u) := by
    simpa only [dist_comm y x] using dist_triangle y x (integerPoint u)
  have hpow : 2 * (2 : ℝ) ^ k₀ ≤ (2 : ℝ) ^ k := by
    calc
      _ = (2 : ℝ) ^ (k₀ + 1) := by rw [pow_succ]; ring
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hkk
  have hpowC := mul_le_mul_of_nonneg_left hpow
    (by positivity : (0 : ℝ) ≤ (C : ℝ) + 1)
  have hC' : (2 : ℝ) ≤ C := by exact_mod_cast hC
  have hCK : 2 * (2 : ℝ) ^ k ≤ (C : ℝ) * (2 : ℝ) ^ k :=
    mul_le_mul_of_nonneg_right hC' (by positivity)
  have hscale : 32 * (2 : ℝ) ^ fineScaleIndex k ≤ (2 : ℝ) ^ k := by
    exact_mod_cast (dyadicScale_side_ratios 5 k (by omega)).1
  nlinarith only [hxu, hyu, htriangle, hpowC, hCK, hscale]

end NearMarkGeometry

end TNLean.PEPS.AreaLaw.Geometry

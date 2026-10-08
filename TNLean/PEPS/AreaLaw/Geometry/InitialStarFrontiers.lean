/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.InitialRegions
import TNLean.PEPS.AreaLaw.Geometry.PrimaryFineCellCover
import TNLean.PEPS.AreaLaw.Geometry.FanFrontiers
import TNLean.PEPS.AreaLaw.Geometry.NearMarkGeometry
import TNLean.PEPS.AreaLaw.Geometry.CellSides

/-!
# Initial frontiers near an actual mark

An initial birth-region frontier sufficiently close to an actual fine-cell
mark lies on one of the four allowed lines through that mark. Primitive
boundary segments have marks of their defining cells as endpoints. Contact derives the neighboring
layer and common quarter mesh, whose line clearance excludes supporting
lines that do not pass through the reference mark. The dummy case first
forces the reference layer to be the initial layer.

The conclusion concerns the actual initial identifiers and their frontiers.
It does not assign sectors or identify active rays, and no local boundary
description is supplied as a hypothesis.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `prop:two-families`, lines 154–177,
212–218 and 299–323, and `geometry:initial-stars`, lines 333–370,
especially 352–359.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Differences of points on an allowed affine line have an allowed slope.
Auxiliary to Section 11, `geometry:initial-stars`, lines 352–359. -/
private theorem allowedSlope_sub_of_mem_line {p q v x : ℝ × ℝ}
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

/-- A sufficiently close allowed mesh segment lies on an allowed line through
the reference mesh point. Auxiliary to Section 11, `geometry:initial-stars`,
lines 352–359. -/
private theorem near_mesh_segment_allowed {o : ℝ × ℝ} {d : ℝ} (hd : 0 < d)
    {p q v x : ℝ × ℝ} (hp : p ∈ affineMesh o d) (hq : q ∈ affineMesh o d)
    (hv : v ∈ affineMesh o d) (hs : IsAllowedSlope (q - p))
    (hx : x ∈ segment ℝ p q) (hnear : dist v x < d / 2) :
    IsAllowedSlope (x - v) := by
  have hxline : x ∈ affineSpan ℝ {p, q} := by
    rw [segment_eq_image_lineMap ℝ] at hx
    obtain ⟨r, _, rfl⟩ := hx
    exact AffineMap.lineMap_mem_affineSpan_pair _ _ _
  have hvline : v ∈ affineSpan ℝ {p, q} := by
    by_contra hout
    exact (not_le_of_gt hnear) (affineMesh_line_dist_ge hd hp hq hv hs hout hxline)
  exact allowedSlope_sub_of_mem_line hs hvline hxline

/-- One cell's marks inherit the existing quarter-mesh inclusion.
Auxiliary to Section 11, `geometry:initial-stars`, lines 352–359. -/
private theorem marks_subset_quarter_mesh (o : ℝ × ℝ) (ℓ j : ℕ)
    (z : ℤ × ℤ) (hℓj : ℓ ≤ j + 1) :
    (beltCellMarks o j z : Set (ℝ × ℝ)) ⊆ affineMesh o ((2 : ℝ) ^ ℓ / 4) := by
  classical
  simpa only [beltMarks, Finset.singleton_biUnion] using
    beltMarks_subset_affineMesh o ℓ j {z} hℓj

/-- The base and last radial edge have the slopes carried by the actual
triangle constructor. Auxiliary to Section 11, `prop:two-families`,
lines 308–310, and `geometry:initial-stars`, lines 352–359. -/
private theorem triangle_base_and_last_slopes (P : TemplatePolygon) :
    match P with
    | .triangle a b c _ _ _ _ => IsAllowedSlope (c - b) ∧ IsAllowedSlope (a - c)
    | .rectangle _ _ _ _ _ _ _ _ => True := by
  cases P with
  | triangle _ _ _ _ _ hbc hca => exact ⟨hbc, hca⟩
  | rectangle => trivial

/-- A whole cell-side contact close to a common-mesh mark has an allowed
direction from that mark. Auxiliary to Section 11, `geometry:initial-stars`,
lines 352–359. -/
private theorem cell_frontier_near_mesh_allowed (o : ℝ × ℝ) (ℓ : ℕ)
    (z : ℤ × ℤ) {d : ℝ} (hd : 0 < d) {v x : ℝ × ℝ}
    (hmarks : (beltCellMarks o ℓ z : Set (ℝ × ℝ)) ⊆ affineMesh o d)
    (hv : v ∈ affineMesh o d) (hx : x ∈ frontier (dyadicCell o ℓ z))
    (hnear : dist v x < d / 2) : IsAllowedSlope (x - v) := by
  obtain ⟨s, hs⟩ := exists_dyadicCellSide_of_mem_frontier o ℓ z x hx
  have hvertices := (cellFan_vertices_mem_beltCellMarks o ℓ z (fun _ ↦ false)).2 ⟨s, 0⟩
  have hslopes := triangle_base_and_last_slopes
    (cellFanPolygon o ℓ z (fun _ ↦ false) ⟨s, 0⟩)
  exact near_mesh_segment_allowed hd (hmarks hvertices.1) (hmarks hvertices.2)
    hv hslopes.1 hs hnear

/-- A nearby point of an actual closed fine cell derives the quarter mesh
for that cell's marks and the reference mark.
Auxiliary to Section 11, `geometry:initial-stars`, lines 352–359. -/
private theorem fine_cell_near_mesh
    (o : ℝ × ℝ) (k h : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (z w : ℤ × ℤ) (v x : ℝ × ℝ) (hC : 2 ≤ C) (hk : 50000000 ≤ k)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (hw : w ∈ fineLayerIndices o h (fineScaleIndex h) Z C)
    (hv : v ∈ beltCellMarks o (fineScaleIndex k) z)
    (hx : x ∈ closure (dyadicCell o (fineScaleIndex h) w))
    (hnear : dist v x < (2 : ℝ) ^ fineScaleIndex k / 32) :
    ((beltCellMarks o (fineScaleIndex k) z : Set (ℝ × ℝ)) ∪
      (beltCellMarks o (fineScaleIndex h) w : Set (ℝ × ℝ))) ⊆
      affineMesh o ((2 : ℝ) ^ fineScaleIndex k / 4) := by
  have ht : 0 < (2 : ℝ) ^ fineScaleIndex k := pow_pos zero_lt_two _
  have hxball : x ∈ Metric.closedBall v (10 * (2 : ℝ) ^ fineScaleIndex k) :=
    Metric.mem_closedBall'.mpr (by linarith)
  exact (fineLayer_near_mark_quarter_mesh o k h Z C z w v hC hk hz hw hv
    ⟨x, hx, hxball⟩).2.2

/-- An actual fine-square frontier point sufficiently close to a reference
mark lies on an allowed line through it. Auxiliary to Section 11,
`geometry:initial-stars`, lines 352–359. -/
private theorem fine_cell_frontier_near_allowed
    (o : ℝ × ℝ) (k h : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (z w : ℤ × ℤ) (v x : ℝ × ℝ) (hC : 2 ≤ C) (hk : 50000000 ≤ k)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (hw : w ∈ fineLayerIndices o h (fineScaleIndex h) Z C)
    (hv : v ∈ beltCellMarks o (fineScaleIndex k) z)
    (hx : x ∈ frontier (dyadicCell o (fineScaleIndex h) w))
    (hnear : dist v x < (2 : ℝ) ^ fineScaleIndex k / 32) :
    IsAllowedSlope (x - v) := by
  have hmesh := fine_cell_near_mesh o k h Z C z w v x hC hk hz hw hv
    (frontier_subset_closure hx) hnear
  have ht : 0 < (2 : ℝ) ^ fineScaleIndex k := pow_pos zero_lt_two _
  exact cell_frontier_near_mesh_allowed o (fineScaleIndex h) w
    (by positivity : 0 < (2 : ℝ) ^ fineScaleIndex k / 4)
    (fun y hy ↦ hmesh (Or.inr hy)) (hmesh (Or.inl hv)) hx (by linarith)

/-- Every actual fan frontier reduces to an outer side or a carried radial
segment. Auxiliary to Section 11, `prop:two-families`, lines 308–323,
and `geometry:initial-stars`, lines 352–359. -/
private theorem fine_fan_frontier_near_allowed
    (o : ℝ × ℝ) (k h : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (z w : ℤ × ℤ) (v x : ℝ × ℝ) (split : Fin 4 → Bool) (j : CellFanSlot split)
    (hC : 2 ≤ C) (hk : 50000000 ≤ k)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (hw : w ∈ fineLayerIndices o h (fineScaleIndex h) Z C)
    (hv : v ∈ beltCellMarks o (fineScaleIndex k) z)
    (hx : x ∈ frontier (cellFanPolygon o (fineScaleIndex h) w split j).region)
    (hnear : dist v x < (2 : ℝ) ^ fineScaleIndex k / 32) :
    IsAllowedSlope (x - v) := by
  rcases cellFanPolygon_frontier_subset_outer_and_radials o (fineScaleIndex h)
      w split j hx with hxcell | hxradial
  · exact fine_cell_frontier_near_allowed o k h Z C z w v x hC hk hz hw hv hxcell hnear
  · obtain ⟨l, hxl⟩ := Set.mem_iUnion.mp hxradial
    have hsub : (cellFanPolygon o (fineScaleIndex h) w split j).region ⊆
        closure (dyadicCell o (fineScaleIndex h) w) := by
      intro y hy
      exact (cellFanPolygons_cover o (fineScaleIndex h) w split) ▸
        Set.mem_iUnion.mpr ⟨j, hy⟩
    have hxcell := closure_minimal hsub isClosed_closure (frontier_subset_closure hx)
    have hmesh := fine_cell_near_mesh o k h Z C z w v x hC hk hz hw hv hxcell hnear
    have hvertices := cellFan_vertices_mem_beltCellMarks o (fineScaleIndex h) w split
    have hslopes := triangle_base_and_last_slopes
      (cellFanPolygon o (fineScaleIndex h) w split l)
    have ht : 0 < (2 : ℝ) ^ fineScaleIndex k := pow_pos zero_lt_two _
    rw [segment_symm] at hxl
    exact near_mesh_segment_allowed
      (by positivity : 0 < (2 : ℝ) ^ fineScaleIndex k / 4)
      (hmesh (Or.inr (hvertices.2 l).2)) (hmesh (Or.inr hvertices.1))
      (hmesh (Or.inl hv)) hslopes.2 hxl (by linarith)

/-- A nearby dummy frontier forces the initial reference layer; its coarse
side endpoints then belong to the same quarter mesh.
Auxiliary to Section 11, `geometry:initial-stars`, lines 352–359,
and `geometry:layer-distance`, lines 179–191. -/
private theorem dummy_frontier_near_allowed
    (o : ℝ × ℝ) (k₀ k : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (z : ℤ × ℤ) (v x : ℝ × ℝ) (hC : 2 ≤ C) (hk : 50000000 ≤ k) (hk₀ : k₀ ≤ k)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (hv : v ∈ beltCellMarks o (fineScaleIndex k) z)
    (hx : x ∈ frontier (closure (dyadicNeighborhood o k₀ Z C)))
    (hnear : dist v x < (2 : ℝ) ^ fineScaleIndex k / 32) :
    IsAllowedSlope (x - v) := by
  have hxN : x ∈ closure (dyadicNeighborhood o k₀ Z C) := by
    simpa only [closure_closure] using frontier_subset_closure hx
  have hvD : v ∈ closure (dyadicLayer o k Z C) :=
    closure_mono (dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices o k
      (fineScaleIndex k) Z C z (fineScaleIndex_le k) hz)
      (beltCellMarks_subset_closure_dyadicCell o (fineScaleIndex k) z hv)
  have ht : 0 < (2 : ℝ) ^ fineScaleIndex k := pow_pos zero_lt_two _
  have hkeq : k = k₀ := by
    by_contra hne
    have hsep := dyadicNeighborhood_dist_later_layer_fineScale o k₀ k Z C x v
      hC hk (by omega) hxN hvD
    rw [dist_comm x v] at hsep
    linarith
  have hfront := frontier_closure_subset hx
  rw [dyadicNeighborhood] at hfront
  obtain ⟨w, _, hxw⟩ := Set.mem_iUnion₂.mp
    ((ambientDilation (occupiedCellIndices o k₀ Z) C).frontier_biUnion_subset
      (dyadicCell o k₀) hfront)
  have hmarks := marks_subset_quarter_mesh o (fineScaleIndex k) k₀ w
    (by have := fineScaleIndex_le k; omega)
  have hvmesh := marks_subset_quarter_mesh o (fineScaleIndex k) (fineScaleIndex k) z
    (by omega) hv
  exact cell_frontier_near_mesh_allowed o k₀ w
    (by positivity : 0 < (2 : ℝ) ^ fineScaleIndex k / 4) hmarks hvmesh hxw
    (by linarith)

/-- An actual initial birth frontier within one thirty-second of a reference
fine-cell side lies on an allowed line through the actual reference mark.
Source: Section 11, `geometry:initial-stars`, lines 333–370, especially 352–359;
the actual initial identifiers are constructed in `prop:two-families`,
lines 154–177, 212–218 and 299–323. -/
theorem initialBirthRegion_frontier_near_mark_allowed
    (o : ℝ × ℝ) (k₀ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (h : ℕ) → Fin (2 ^ (pitchScaleIndex h - fineScaleIndex h)))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (k : ℕ) (z : ℤ × ℤ) (v x : ℝ × ℝ)
    (hk₀ : k₀ ≤ k) (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (hv : v ∈ beltCellMarks o (fineScaleIndex k) z)
    (i : InitialRegionIndex o k₀ Z C a b hC h₀)
    (hx : x ∈ frontier (initialBirthRegion o k₀ Z C a b hC h₀ i))
    (hnear : dist v x < (2 : ℝ) ^ fineScaleIndex k / 32) :
    IsAllowedSlope (x - v) := by
  classical
  have hk : 50000000 ≤ k := h₀.trans hk₀
  rcases i with u | (⟨h, J⟩ | ⟨h, w, R⟩)
  · exact dummy_frontier_near_allowed o k₀ k Z C z v x hC hk hk₀ hz hv hx hnear
  · change x ∈ frontier (primaryBirthRegion o h.val (fineScaleIndex h.val)
      (pitchScaleIndex h.val) Z C (a h.val).val (b h.val).val J.val) at hx
    rw [primaryBirthRegion_eq_iUnion_nonbeltCell_closure o h.val (fineScaleIndex h.val)
      (pitchScaleIndex h.val) Z C (a h.val) (b h.val) J.val (fineScaleIndex_le h.val)
      ((fineScaleIndex_le h.val).trans (le_pitchScaleIndex h.val))] at hx
    let F := (fineLayerIndices o h.val (fineScaleIndex h.val) Z C).filter (fun w ↦
      w ∉ beltCellIndices (fineLayerIndices o h.val (fineScaleIndex h.val) Z C)
        (2 ^ (pitchScaleIndex h.val - fineScaleIndex h.val)) (a h.val) (b h.val) ∧
      nonbeltPitchIndex (fineScaleIndex h.val) (pitchScaleIndex h.val)
        (a h.val).val (b h.val).val w = J.val)
    change x ∈ frontier (⋃ w ∈ F, closure (dyadicCell o (fineScaleIndex h.val) w)) at hx
    obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp
      (F.frontier_biUnion_subset (fun w ↦ closure (dyadicCell o (fineScaleIndex h.val) w)) hx)
    exact fine_cell_frontier_near_allowed o k h.val Z C z w v x hC hk hz
      (Finset.mem_filter.mp hw).1 hv (frontier_closure_subset hxw) hnear
  · change x ∈ frontier (cellFanRunRegion o (fineScaleIndex h.val) w.val
      (fineLayerSplitMask o k₀ h.val Z C w.val)
      (beltCellFanColor o k₀ Z C a b h.val w.val hC h₀ h.property w.property) R) at hx
    rw [cellFanRunRegion] at hx
    obtain ⟨j, _, hxj⟩ := Set.mem_iUnion₂.mp
      ((Set.toFinite R.supp).frontier_biUnion_subset
        (fun j ↦ (cellFanPolygon o (fineScaleIndex h.val) w.val
          (fineLayerSplitMask o k₀ h.val Z C w.val) j).region) hx)
    exact fine_fan_frontier_near_allowed o k h.val Z C z w.val v x
      (fineLayerSplitMask o k₀ h.val Z C w.val) j hC hk hz
      (Finset.mem_filter.mp w.property).1 hv hxj hnear

end TNLean.PEPS.AreaLaw.Geometry

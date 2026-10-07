/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.MeshGeometry
import TNLean.PEPS.AreaLaw.Geometry.LocalLayers
import TNLean.PEPS.AreaLaw.Geometry.AdjacentScales
import TNLean.PEPS.AreaLaw.Geometry.LayerPartition

/-!
# Separation of actual fine-layer marks

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

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript:
  preprints/
  A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
  build/
  sections/
  10-geometry.tex
Labels: prop:two-families; geometry:initial-stars; geometry:nonadjacent.
Source lines: 325–339; 352–359; 193–204 for nonadjacent layers.
Source revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.finelayer_marks_dist_ge
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.fineLayer_marks_dist_ge
-/

namespace TNLean.PEPS.AreaLaw.Geometry

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

end TNLean.PEPS.AreaLaw.Geometry

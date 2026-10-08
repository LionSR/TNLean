/-
Original formalization from the cited manuscript;
no upstream Lean proof text reused.
Manuscript: OpenAI, A two-dimensional area law from a global spectral gap,
September 24, 2026.
Pinned source: adc7f1241b42e322a6451854ab7e4b4c146bf78a
Manuscript path:
preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/10-geometry.tex

Provenance-ID: 8758-tnlean.peps.arealaw.geometry.near_mark_quarter_mesh
Downstream declaration:
TNLean.PEPS.AreaLaw.Geometry.fineLayer_near_mark_quarter_mesh
Source labels: geometry:initial-stars
Source: Section 11, geometry:initial-stars, lines 352–359.

Provenance-ID: 8758-tnlean.peps.arealaw.geometry.dummy_later_fine_separation
Downstream declaration:
TNLean.PEPS.AreaLaw.Geometry.dyadicNeighborhood_dist_later_layer_fineScale
Source labels: geometry:initial-stars, geometry:layer-distance
Source: Section 11, geometry:initial-stars, lines 352–359; geometry:layer-distance, lines 179–191;
scale comparison, lines 200–207.

OpenAI Codex (GPT-6) assistance was used in this formalization.
-/
/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.AdjacentScales
import TNLean.PEPS.AreaLaw.Geometry.DummyContacts
import TNLean.PEPS.AreaLaw.Geometry.LayerPartition
import TNLean.PEPS.AreaLaw.Geometry.LocalLayers
import TNLean.PEPS.AreaLaw.Geometry.MeshGeometry

/-!
# Actual layers and meshes near a fine-cell mark

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

namespace TNLean.PEPS.AreaLaw.Geometry

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

end TNLean.PEPS.AreaLaw.Geometry

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.PrimaryRegions

/-!
# Closed rectangular fragments of primary birth regions

Intersecting a pitch interior with each of the half-open cells of an actual
dyadic layer gives finitely many fragments. A nonempty fragment has a closed
rectangular closure, with diameter at most the layer-cell side. Their union
is precisely the primary birth region; disconnected fragments are retained
under the same primary identifier.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:primary-pieces`, lines 212–218
and 237–249. Source revision:
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
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
Labels: geometry:primary-pieces.
Source lines: 212–218, 237–249.
Source revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.primarybirthregion_eq_iunion_primaryfragment
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.primaryBirthRegion_eq_iUnion_primaryFragment
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.primaryfragment_eq_closedrectangle
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.primaryFragment_eq_closedRectangle
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.primaryfragment_subset_closure_dyadiccell
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.primaryFragment_subset_closure_dyadicCell
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.primaryfragment_dist_le
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.primaryFragment_dist_le
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.primaryfragment_diam_le
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.primaryFragment_diam_le
-/

namespace TNLean.PEPS.AreaLaw.Geometry

private theorem closure_Ico_inter_Ioo_of_nonempty {a b c d : ℝ}
    (h : (Set.Ico a b ∩ Set.Ioo c d).Nonempty) :
    closure (Set.Ico a b ∩ Set.Ioo c d) = Set.Icc (max a c) (min b d) := by
  have hab : max a c < min b d := by
    obtain ⟨x, hx⟩ := h
    exact (max_le hx.1.1 hx.2.1.le).trans_lt (lt_min hx.1.2 hx.2.2)
  apply Set.Subset.antisymm
  · apply closure_minimal _ isClosed_Icc
    intro x hx
    exact ⟨max_le hx.1.1 hx.2.1.le, le_min hx.1.2.le hx.2.2.le⟩
  · rw [← closure_Ioo hab.ne]
    apply closure_mono
    intro x hx
    exact ⟨⟨(le_max_left a c).trans hx.1.le, hx.2.trans_le (min_le_left b d)⟩,
      ⟨(le_max_right a c).trans_lt hx.1, hx.2.trans_le (min_le_right b d)⟩⟩

/-- A primary birth region is exactly the finite union of its nonempty cell fragments.
Source: area-law Section 11, lines 215–218 and `geometry:primary-pieces`, lines 239–246. -/
theorem primaryBirthRegion_eq_iUnion_primaryFragment (o : ℝ × ℝ) (k ℓ p : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (a b : ℤ) (j : ℤ × ℤ) :
    primaryBirthRegion o k ℓ p Z C a b j =
      ⋃ z ∈ primaryFragmentIndices o k ℓ p Z C a b j,
        primaryFragment o k ℓ p a b j z := by
  classical
  rw [primaryBirthRegion, dyadicLayer_eq_iUnion, Set.iUnion₂_inter,
    Finset.closure_biUnion]
  ext x
  simp only [Set.mem_iUnion, primaryFragmentIndices, Finset.mem_filter, primaryFragment]
  constructor
  · rintro ⟨z, hz, hx⟩
    exact ⟨z, ⟨hz, closure_nonempty_iff.mp ⟨x, hx⟩⟩, hx⟩
  · rintro ⟨z, ⟨hz, _⟩, hx⟩
    exact ⟨z, hz, hx⟩

/-- A nonempty cell intersection gives the closed rectangle obtained by clipping
the cell and pitch intervals. Source: area-law Section 11, `geometry:primary-pieces`,
lines 239–246. -/
theorem primaryFragment_eq_closedRectangle (o : ℝ × ℝ) (k ℓ p : ℕ)
    (a b : ℤ) (j z : ℤ × ℤ)
    (h : (dyadicCell o k z ∩ pitchInterior o ℓ p a b j).Nonempty) :
    primaryFragment o k ℓ p a b j z =
      Set.Icc
        (max (o.1 + (2 : ℝ) ^ k * z.1)
          (o.1 + (2 : ℝ) ^ ℓ * a + (2 : ℝ) ^ p * j.1 + (2 : ℝ) ^ ℓ))
        (min (o.1 + (2 : ℝ) ^ k * (z.1 + 1))
          (o.1 + (2 : ℝ) ^ ℓ * a + (2 : ℝ) ^ p * j.1 + (2 : ℝ) ^ p)) ×ˢ
      Set.Icc
        (max (o.2 + (2 : ℝ) ^ k * z.2)
          (o.2 + (2 : ℝ) ^ ℓ * b + (2 : ℝ) ^ p * j.2 + (2 : ℝ) ^ ℓ))
        (min (o.2 + (2 : ℝ) ^ k * (z.2 + 1))
          (o.2 + (2 : ℝ) ^ ℓ * b + (2 : ℝ) ^ p * j.2 + (2 : ℝ) ^ p)) := by
  change (Set.Ico _ _ ×ˢ Set.Ico _ _ ∩ Set.Ioo _ _ ×ˢ Set.Ioo _ _).Nonempty at h
  rw [Set.prod_inter_prod, Set.prod_nonempty_iff] at h
  unfold primaryFragment dyadicCell pitchInterior
  rw [Set.prod_inter_prod, closure_prod_eq,
    closure_Ico_inter_Ioo_of_nonempty h.1, closure_Ico_inter_Ioo_of_nonempty h.2]

/-- Every closed primary fragment lies in the closed layer cell from which it was cut.
Source: area-law Section 11, `geometry:primary-pieces`, lines 243–246. -/
theorem primaryFragment_subset_closure_dyadicCell (o : ℝ × ℝ) (k ℓ p : ℕ)
    (a b : ℤ) (j z : ℤ × ℤ) :
    primaryFragment o k ℓ p a b j z ⊆ closure (dyadicCell o k z) :=
  closure_mono Set.inter_subset_left

/-- Two points of a closed primary fragment have sup distance at most one layer-cell side.
Source: area-law Section 11, `geometry:primary-pieces`, lines 243–246. -/
theorem primaryFragment_dist_le (o : ℝ × ℝ) (k ℓ p : ℕ)
    (a b : ℤ) (j z : ℤ × ℤ) (x y : ℝ × ℝ)
    (hx : x ∈ primaryFragment o k ℓ p a b j z)
    (hy : y ∈ primaryFragment o k ℓ p a b j z) :
    dist x y ≤ (2 : ℝ) ^ k := by
  simpa using dyadicCell_dist_le o k z z 0 x y
    (primaryFragment_subset_closure_dyadicCell o k ℓ p a b j z hx)
    (primaryFragment_subset_closure_dyadicCell o k ℓ p a b j z hy) (by simp)

/-- The sup diameter of a closed primary fragment is at most one layer-cell side.
Source: area-law Section 11, `geometry:primary-pieces`, lines 243–246. -/
theorem primaryFragment_diam_le (o : ℝ × ℝ) (k ℓ p : ℕ)
    (a b : ℤ) (j z : ℤ × ℤ) :
    Metric.diam (primaryFragment o k ℓ p a b j z) ≤ (2 : ℝ) ^ k :=
  Metric.diam_le_of_forall_dist_le (pow_nonneg (by norm_num) k)
    (fun x hx y hy ↦ primaryFragment_dist_le o k ℓ p a b j z x y hx hy)

end TNLean.PEPS.AreaLaw.Geometry

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.PrimaryCounting
import TNLean.PEPS.AreaLaw.Geometry.FineBelts
import Mathlib.Data.Int.ModEq

/-!
# Primary birth regions of non-belt fine cells

A fine-layer cell outside the selected vertical and horizontal belt residues
has a unique primary identifier. Its closed square is contained in that primary
birth region. The open cell interior lies in the open pitch interior; taking
closures then includes the cell sides without assigning an interface point to
an open region.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, lines 212–218, 237–249 and 299–305.
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
Labels: prop:two-families; geometry:primary-pieces.
Source lines: 212–218; 237–249; 299–305.
Source revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.nonbeltpitchindex
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.nonbeltPitchIndex
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.closure_nonbeltcell_subset_primarybirthregion
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.closure_nonbeltCell_subset_primaryBirthRegion
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.exists_unique_primary_of_nonbeltcell
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.exists_unique_primary_of_nonbeltCell
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The pitch-square index of a fine cell, relative to the two selected shifts.
Source: area-law Section 11, lines 212–218 and 299–305. -/
def nonbeltPitchIndex (ℓ p : ℕ) (a b : ℤ) (z : ℤ × ℤ) : ℤ × ℤ :=
  ((z.1 - a) / (2 : ℤ) ^ (p - ℓ), (z.2 - b) / (2 : ℤ) ^ (p - ℓ))

private theorem nonbelt_coordinate_bounds (m : ℕ) (a : Fin m) (z : ℤ)
    (hne : z % (m : ℤ) ≠ (a.val : ℤ)) :
    (a.val : ℤ) + (m : ℤ) * ((z - a.val) / m) + 1 ≤ z ∧
      z + 1 ≤ (a.val : ℤ) + (m : ℤ) * ((z - a.val) / m) + m := by
  have hm : (0 : ℤ) < m := by exact_mod_cast (show 0 < m by omega)
  have ha : (a.val : ℤ) % m = a.val :=
    Int.emod_eq_of_lt (by omega) (by exact_mod_cast a.isLt)
  have hrne : (z - a.val) % (m : ℤ) ≠ 0 := by
    intro he
    apply hne
    exact (Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr he).trans ha
  have hrlo := Int.emod_nonneg (z - a.val) hm.ne'
  have hrhi := Int.emod_lt_of_pos (z - a.val) hm
  have he := Int.mul_ediv_add_emod (z - a.val) (m : ℤ)
  omega

private theorem nonbelt_coordinate_mem_pitch {o t s x : ℝ}
    (m : ℕ) (a : Fin m) (z : ℤ) (ht : 0 < t) (hs : s = t * m)
    (hne : z % (m : ℤ) ≠ (a.val : ℤ))
    (hx : x ∈ Set.Ioo (o + t * z) (o + t * (z + 1))) :
    x ∈ Set.Ioo (o + t * a.val + s * ((z - a.val) / (m : ℤ) : ℤ) + t)
      (o + t * a.val + s * ((z - a.val) / (m : ℤ) : ℤ) + s) := by
  obtain ⟨hlo, hhi⟩ := nonbelt_coordinate_bounds m a z hne
  have hlo' : (a.val : ℝ) + (m : ℝ) * (((z - a.val) / (m : ℤ) : ℤ) : ℝ) + 1 ≤ z := by
    exact_mod_cast hlo
  have hhi' : (z : ℝ) + 1 ≤ (a.val : ℝ) +
      (m : ℝ) * (((z - a.val) / (m : ℤ) : ℤ) : ℝ) + m := by exact_mod_cast hhi
  rw [hs]
  constructor
  · nlinarith [hx.1, mul_le_mul_of_nonneg_left hlo' ht.le]
  · nlinarith [hx.2, mul_le_mul_of_nonneg_left hhi' ht.le]

private theorem cell_interior_nonempty (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ) :
    (interior (dyadicCell o ℓ z)).Nonempty := by
  have ht : 0 < (2 : ℝ) ^ ℓ := by positivity
  have h (v : ℝ) (j : ℤ) : v + (2 : ℝ) ^ ℓ * j <
      v + (2 : ℝ) ^ ℓ * (j + 1) := by nlinarith
  rw [dyadicCell, interior_prod_eq, interior_Ico, interior_Ico]
  exact (Set.nonempty_Ioo.mpr (h o.1 z.1)).prod (Set.nonempty_Ioo.mpr (h o.2 z.2))

private theorem closure_cell_interior (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ) :
    closure (interior (dyadicCell o ℓ z)) = closure (dyadicCell o ℓ z) := by
  have ht : 0 < (2 : ℝ) ^ ℓ := by positivity
  have h (v : ℝ) (j : ℤ) : v + (2 : ℝ) ^ ℓ * j ≠
      v + (2 : ℝ) ^ ℓ * (j + 1) := by nlinarith
  rw [closure_dyadicCell, dyadicCell, interior_prod_eq, interior_Ico, interior_Ico,
    closure_prod_eq, closure_Ioo (h o.1 z.1), closure_Ioo (h o.2 z.2)]

private theorem nonbelt_cell_interior_subset (o : ℝ × ℝ) (k ℓ p : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (a b : Fin (2 ^ (p - ℓ))) (z : ℤ × ℤ)
    (hℓk : ℓ ≤ k) (hℓp : ℓ ≤ p) (hz : z ∈ fineLayerIndices o k ℓ Z C)
    (hnot : z ∉ beltCellIndices (fineLayerIndices o k ℓ Z C) (2 ^ (p - ℓ)) a b) :
    interior (dyadicCell o ℓ z) ⊆ dyadicLayer o k Z C ∩
      pitchInterior o ℓ p a.val b.val (nonbeltPitchIndex ℓ p a.val b.val z) := by
  classical
  have hres : z.1 % ((2 ^ (p - ℓ) : ℕ) : ℤ) ≠ (a.val : ℤ) ∧
      z.2 % ((2 ^ (p - ℓ) : ℕ) : ℤ) ≠ (b.val : ℤ) := by
    simpa only [beltCellIndices, Finset.mem_filter, hz, true_and, not_or] using hnot
  have hcell : dyadicCell o ℓ z ⊆ dyadicLayer o k Z C := by
    intro x hx
    rw [dyadicLayer_eq_iUnion_fine o k ℓ Z C hℓk]
    exact Set.mem_iUnion₂.mpr ⟨z, hz, hx⟩
  have hs : (2 : ℝ) ^ p = (2 : ℝ) ^ ℓ * (2 ^ (p - ℓ) : ℕ) := by
    push_cast
    rw [← pow_add, Nat.add_sub_of_le hℓp]
  intro x hx
  refine ⟨hcell (interior_subset hx), ?_⟩
  rw [dyadicCell, interior_prod_eq, interior_Ico, interior_Ico] at hx
  exact ⟨by simpa [pitchInterior, nonbeltPitchIndex] using
    nonbelt_coordinate_mem_pitch (2 ^ (p - ℓ)) a z.1 (by positivity) hs hres.1 hx.1,
    by simpa [pitchInterior, nonbeltPitchIndex] using
    nonbelt_coordinate_mem_pitch (2 ^ (p - ℓ)) b z.2 (by positivity) hs hres.2 hx.2⟩

/-- The closed square of an actual non-belt fine cell lies in its primary birth region.
The proof first uses the open cell interior, whose closure is the whole closed square.
Source: area-law Section 11, lines 212–218, 237–249 and 299–305. -/
theorem closure_nonbeltCell_subset_primaryBirthRegion (o : ℝ × ℝ) (k ℓ p : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (a b : Fin (2 ^ (p - ℓ))) (z : ℤ × ℤ)
    (hℓk : ℓ ≤ k) (hℓp : ℓ ≤ p) (hz : z ∈ fineLayerIndices o k ℓ Z C)
    (hnot : z ∉ beltCellIndices (fineLayerIndices o k ℓ Z C) (2 ^ (p - ℓ)) a b) :
    closure (dyadicCell o ℓ z) ⊆
      primaryBirthRegion o k ℓ p Z C a.val b.val (nonbeltPitchIndex ℓ p a.val b.val z) := by
  rw [← closure_cell_interior]
  exact closure_mono (nonbelt_cell_interior_subset o k ℓ p Z C a b z hℓk hℓp hz hnot)

/-- An actual non-belt fine cell belongs to a unique retained primary identifier.
Source: area-law Section 11, lines 212–218, 237–249 and 299–305. -/
theorem exists_unique_primary_of_nonbeltCell (o : ℝ × ℝ) (k ℓ p : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (a b : Fin (2 ^ (p - ℓ))) (z : ℤ × ℤ)
    (hℓk : ℓ ≤ k) (hℓp : ℓ ≤ p) (hz : z ∈ fineLayerIndices o k ℓ Z C)
    (hnot : z ∉ beltCellIndices (fineLayerIndices o k ℓ Z C) (2 ^ (p - ℓ)) a b) :
    ∃! j, j ∈ primaryPitchIndices o k ℓ p Z C a.val b.val ∧
      closure (dyadicCell o ℓ z) ⊆ primaryBirthRegion o k ℓ p Z C a.val b.val j := by
  have hsub := nonbelt_cell_interior_subset o k ℓ p Z C a b z hℓk hℓp hz hnot
  obtain ⟨x, hx⟩ := cell_interior_nonempty o ℓ z
  have hclosed : x ∈ closure (dyadicCell o ℓ z) := subset_closure (interior_subset hx)
  have hbirth := closure_nonbeltCell_subset_primaryBirthRegion o k ℓ p Z C a b z
    hℓk hℓp hz hnot
  refine ⟨nonbeltPitchIndex ℓ p a.val b.val z, ⟨?_, hbirth⟩, ?_⟩
  · exact (mem_primaryPitchIndices_iff o k ℓ p Z C a.val b.val _).mpr ⟨x, hsub hx⟩
  · intro j hj
    by_contra hne
    have hsep := primaryBirthRegion_dist_separation o k ℓ p Z C a.val b.val j
      (nonbeltPitchIndex ℓ p a.val b.val z) hne x x (hj.2 hclosed) (hbirth hclosed)
    have ht : 0 < (2 : ℝ) ^ ℓ := by positivity
    rw [dist_self] at hsep
    exact not_le_of_gt ht hsep

end TNLean.PEPS.AreaLaw.Geometry

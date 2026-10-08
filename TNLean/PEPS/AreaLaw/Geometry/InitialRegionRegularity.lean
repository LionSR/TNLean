/-
Original formalization from the cited manuscript;
no upstream Lean proof text reused.
Manuscript: OpenAI, A two-dimensional area law from a global spectral gap,
September 24, 2026.
Pinned source: adc7f1241b42e322a6451854ab7e4b4c146bf78a
Manuscript path:
preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/10-geometry.tex

Provenance-ID: 8758-tnlean.peps.arealaw.geometry.initial_birth_regularity
Downstream declaration:
TNLean.PEPS.AreaLaw.Geometry.initialBirthRegion_eq_closure_initialOpenRegion
Source labels: prop:two-families
Source: Section 11, prop:two-families, lines 154–177, 212–218 and 299–323, especially 308–316.

OpenAI Codex (GPT-6) assistance was used in this formalization.
-/
/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.InitialRegions
import TNLean.PEPS.AreaLaw.Geometry.FanRegularity
import TNLean.PEPS.AreaLaw.Geometry.PrimaryFineCellCover

/-!
# Regularity of initial birth regions

Each actual initial birth region is the closure of its open interior. The
dummy and primary regions are finite unions of closed dyadic squares; a belt
run is a finite union of nondegenerate closed fan triangles. Finite unions
preserve this regularity, including empty unions and disconnected regions.

The nonzero determinant carried by each triangle implies nonempty interior.
One actual fan triangle supplies the same fact for a closed dyadic square.
No additional nonemptiness or regularity hypothesis is imposed, and no
finiteness of the entire initial family is asserted.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `prop:two-families`, lines 154–177,
212–218 and 299–323, especially 308–316.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- A closed dyadic square is the closure of its interior, which contains
the interior of an actual fan triangle.
Auxiliary to Section 11, `prop:two-families`, lines 154–177 and 299–310. -/
private theorem closed_cell_regular (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ) :
    closure (interior (closure (dyadicCell o ℓ z))) = closure (dyadicCell o ℓ z) := by
  let split : Fin 4 → Bool := fun _ ↦ false
  let i : CellFanSlot split := ⟨0, 0⟩
  have hn := (cellFanPolygon_interior_nonempty_and_closure_eq o ℓ z split i).1
  have hsub : (cellFanPolygon o ℓ z split i).region ⊆
      closure (dyadicCell o ℓ z) := by
    intro x hx
    exact (cellFanPolygons_cover o ℓ z split) ▸ Set.mem_iUnion.mpr ⟨i, hx⟩
  have hint : (interior (closure (dyadicCell o ℓ z))).Nonempty :=
    hn.mono (interior_mono hsub)
  have hconv : Convex ℝ (dyadicCell o ℓ z) := by
    unfold dyadicCell
    exact (convex_Ico _ _).prod (convex_Ico _ _)
  simpa only [closure_closure] using
    hconv.closure.closure_interior_eq_closure_of_nonempty_interior hint

/-- A finite union of regions equal to the closures of their interiors has
the same property, including the empty union.
Auxiliary to Section 11, `prop:two-families`, lines 154–177, 212–218 and 313–316. -/
private theorem finite_biUnion_regular {ι : Type*} (F : Set ι) (hF : F.Finite)
    (P : ι → Set (ℝ × ℝ))
    (hreg : ∀ i ∈ F, closure (interior (P i)) = P i) :
    closure (interior (⋃ i ∈ F, P i)) = ⋃ i ∈ F, P i := by
  have hclosed : ∀ i ∈ F, IsClosed (P i) := by
    intro i hi
    rw [← hreg i hi]
    exact isClosed_closure
  apply Set.Subset.antisymm
  · exact closure_minimal interior_subset (hF.isClosed_biUnion hclosed)
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    rw [← hreg i hi] at hxi
    exact closure_mono (interior_mono (fun y hy ↦ Set.mem_iUnion₂.mpr ⟨i, hi, hy⟩)) hxi

/-- Every actual initial birth region is the closure of its initial open
interior. Empty endpoint sets and empty or disconnected regions are allowed.
Source: Section 11, `prop:two-families`, lines 154–177, 212–218 and 299–323,
especially 308–316. -/
theorem initialBirthRegion_eq_closure_initialOpenRegion
    (o : ℝ × ℝ) (k₀ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k)))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (i : InitialRegionIndex o k₀ Z C a b hC h₀) :
    initialBirthRegion o k₀ Z C a b hC h₀ i =
      closure (initialOpenRegion o k₀ Z C a b hC h₀ i) := by
  classical
  rcases i with ⟨⟩ | (⟨k, J⟩ | ⟨k, z, R⟩)
  · change closure (dyadicNeighborhood o k₀ Z C) =
      closure (interior (closure (dyadicNeighborhood o k₀ Z C)))
    have hN : closure (dyadicNeighborhood o k₀ Z C) =
        ⋃ w ∈ ambientDilation (occupiedCellIndices o k₀ Z) C,
          closure (dyadicCell o k₀ w) := by
      rw [dyadicNeighborhood, Finset.closure_biUnion]
    simp only [hN]
    exact (finite_biUnion_regular _ (Finset.finite_toSet _)
      (fun w ↦ closure (dyadicCell o k₀ w))
      (fun w _ ↦ closed_cell_regular o k₀ w)).symm
  · change primaryBirthRegion o k.val (fineScaleIndex k.val) (pitchScaleIndex k.val)
        Z C (a k.val).val (b k.val).val J.val =
      closure (interior (primaryBirthRegion o k.val (fineScaleIndex k.val)
        (pitchScaleIndex k.val) Z C (a k.val).val (b k.val).val J.val))
    have hP := primaryBirthRegion_eq_iUnion_nonbeltCell_closure o k.val
      (fineScaleIndex k.val) (pitchScaleIndex k.val) Z C (a k.val) (b k.val) J.val
      (fineScaleIndex_le k.val)
      ((fineScaleIndex_le k.val).trans (le_pitchScaleIndex k.val))
    simp only [hP]
    exact (finite_biUnion_regular _ (Finset.finite_toSet _)
      (fun w ↦ closure (dyadicCell o (fineScaleIndex k.val) w))
      (fun w _ ↦ closed_cell_regular o (fineScaleIndex k.val) w)).symm
  · change cellFanRunRegion o (fineScaleIndex k.val) z.val
        (fineLayerSplitMask o k₀ k.val Z C z.val)
        (beltCellFanColor o k₀ Z C a b k.val z.val hC h₀ k.property z.property) R =
      closure (interior (cellFanRunRegion o (fineScaleIndex k.val) z.val
        (fineLayerSplitMask o k₀ k.val Z C z.val)
        (beltCellFanColor o k₀ Z C a b k.val z.val hC h₀ k.property z.property) R))
    simp only [cellFanRunRegion]
    exact (finite_biUnion_regular R.supp R.supp.toFinite
      (fun j ↦ (cellFanPolygon o (fineScaleIndex k.val) z.val
        (fineLayerSplitMask o k₀ k.val Z C z.val) j).region)
      (fun j _ ↦ (cellFanPolygon_interior_nonempty_and_closure_eq o (fineScaleIndex k.val) z.val
        (fineLayerSplitMask o k₀ k.val Z C z.val) j).2)).symm

end TNLean.PEPS.AreaLaw.Geometry

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.CellFanRays
import TNLean.PEPS.AreaLaw.Geometry.InitialSectorCycle
import TNLean.PEPS.AreaLaw.Geometry.InitialActiveRays

/-!
# Cardinality of the distinct active directed rays near an initial mark

The actual assignment to the eight midpoint sectors determines which
successive sectors have different initial identifiers. The directed rays
at these changes form a finite set with even cardinality at most eight.
Distinct fan endpoints determine distinct directed rays, so taking this
image counts each direction once and keeps antipodal directions distinct.
The actual local frontiers are exactly the radial segments at these changes.
No identification of topological angular components is asserted.

## References

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:initial-stars`, lines 333–370,
especially the opposite labels and single counting in lines 366–370.
Evenness is the consequence of the cyclic binary labels.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Manuscript file:
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/`
`build/sections/10-geometry.tex`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The deduplicated directed rays at changes of the actual initial sector
identifier have even cardinality at most eight. The sector assignment is
derived from the actual initial regions. Source: Section 11,
`geometry:initial-stars`, lines 333–370, especially lines 366–370. -/
theorem initialRegion_active_rays_card_even_and_le_eight
    (o : ℝ × ℝ) (k₀ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (h : ℕ) → Fin (2 ^ (pitchScaleIndex h - fineScaleIndex h)))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (k : ℕ) (z : ℤ × ℤ) (v : ℝ × ℝ) (hk₀ : k₀ ≤ k)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (hv : v ∈ beltCellMarks o (fineScaleIndex k) z) :
    let ℓ := fineScaleIndex k - 5
    let r := (2 : ℝ) ^ ℓ / 2
    let oSmall := (v.1 - r, v.2 - r)
    let J := CellFanSlot (fun _ : Fin 4 ↦ true)
    let σ := Classical.choose
      (exists_unique_initialRegion_sector_assignment
        o k₀ Z C a b hC h₀ k z v hk₀ hz hv)
    let A : Set J := {s | σ s ≠ σ (cellFanNext s)}
    let D := cellFanRay oSmall ℓ (0, 0) (fun _ : Fin 4 ↦ true) '' A
    Even (Nat.card D) ∧ Nat.card D ≤ 8 := by
  classical
  dsimp only
  let J := CellFanSlot (fun _ : Fin 4 ↦ true)
  let σ := Classical.choose
    (exists_unique_initialRegion_sector_assignment
      o k₀ Z C a b hC h₀ k z v hk₀ hz hv)
  let A : Set J := {s | σ s ≠ σ (cellFanNext s)}
  rw [Nat.card_image_of_injective (cellFanRay_injective _ _ _ _) A]
  refine ⟨initialRegion_sector_assignment_changes_even
    o k₀ Z C a b hC h₀ k z v hk₀ hz hv, ?_⟩
  calc
    Nat.card A ≤ Nat.card J :=
      Nat.card_le_card_of_injective (Subtype.val : A → J) Subtype.val_injective
    _ ≤ 8 := by
      simpa only [Nat.card_eq_fintype_card] using
        (card_cellFanSlot_bounds (fun _ : Fin 4 ↦ true)).2

/-- In the open smaller square about an actual fine-cell mark, the initial
birth frontiers are exactly the radial segments at changes of the derived
identifier to its perimeter successor. Source: Section 11,
`geometry:initial-stars`, lines 333–370, especially lines 361–370, and
`prop:two-families`, lines 308–323. -/
theorem initialRegion_frontier_near_mark_iff_active_successor
    (o : ℝ × ℝ) (k₀ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (h : ℕ) → Fin (2 ^ (pitchScaleIndex h - fineScaleIndex h)))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (k : ℕ) (z : ℤ × ℤ) (v : ℝ × ℝ) (hk₀ : k₀ ≤ k)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (hv : v ∈ beltCellMarks o (fineScaleIndex k) z) :
    let ℓ := fineScaleIndex k - 5
    let r := (2 : ℝ) ^ ℓ / 2
    let oSmall := (v.1 - r, v.2 - r)
    let J := CellFanSlot (fun _ : Fin 4 ↦ true)
    let I := InitialRegionIndex o k₀ Z C a b hC h₀
    let σ : J → I := Classical.choose
      (exists_unique_initialRegion_sector_assignment
        o k₀ Z C a b hC h₀ k z v hk₀ hz hv)
    ∀ x ∈ Metric.ball v r,
      (∃ i : I, x ∈ frontier (initialBirthRegion o k₀ Z C a b hC h₀ i)) ↔
      ∃ s : J, σ s ≠ σ (cellFanNext s) ∧
        x ∈ segment ℝ v (cellFanEnd oSmall ℓ (0, 0) (fun _ ↦ true) s) := by
  classical
  dsimp only
  intro x hx
  simpa only [cellFanEnd_eq_cellFanStart_iff, exists_eq_left] using
    initialRegion_frontier_near_mark_iff_active_radial
      o k₀ Z C a b hC h₀ k z v hk₀ hz hv x hx


end TNLean.PEPS.AreaLaw.Geometry

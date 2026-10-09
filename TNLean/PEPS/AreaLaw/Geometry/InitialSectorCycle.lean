/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.CellFanCycle
import TNLean.PEPS.AreaLaw.Geometry.InitialSectorColors
import Mathlib.Data.Finset.SymmDiff
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Group.Even

/-!
# Evenness of actual initial-sector changes

The binary labels on a finite permutation change an even number of times.
For the eight sectors around an actual fine-cell mark, adjacent label changes
are precisely changes of the identifiers assigned by the initial regions.
The assignment is derived from those regions, and the count distinguishes
slots even when several disconnected runs carry the same identifier.

## References

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:initial-stars`, lines 361–370,
and `prop:two-families`, lines 313–323.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Manuscript file:
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/`
`build/sections/10-geometry.tex`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

open scoped symmDiff

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Binary label changes under a finite permutation have even cardinality.
Auxiliary to Section 11, `geometry:initial-stars`, lines 361–370. -/
private theorem binaryPermutation_changes_even
    {J : Type*} [Fintype J] (τ : Equiv.Perm J) (c : J → Fin 2) :
    Even ((Finset.univ.filter (fun s ↦ c s ≠ c (τ s))).card) := by
  classical
  have hbinary : ∀ a b : Fin 2,
      a ≠ b ↔ (a = 0 ∧ b ≠ 0) ∨ (b = 0 ∧ a ≠ 0) := by decide
  let A : Finset J := Finset.univ.filter (fun s ↦ c s = 0)
  let B : Finset J := A.map τ.symm.toEmbedding
  have hmemB : ∀ s, s ∈ B ↔ c (τ s) = 0 := fun s ↦ by simp [B, A]
  have hchange :
      Finset.univ.filter (fun s ↦ c s ≠ c (τ s)) = A ∆ B := by
    ext s
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_symmDiff, A, hmemB] using hbinary (c s) (c (τ s))
  have hcard : A.card = B.card := by simp only [B, Finset.card_map]
  have hdiff : (A \ B).card = (B \ A).card :=
    (Finset.card_sdiff_eq_card_sdiff_iff (s := A) (t := B)).mpr hcard
  have hdis : Disjoint (A \ B) (B \ A) := disjoint_sdiff_sdiff
  refine ⟨(A \ B).card, ?_⟩
  rw [hchange, Finset.symmDiff_def,
    Finset.card_union_of_disjoint hdis, ← hdiff]

/-- The number of changes of the derived initial identifier around the eight
midpoint sectors is even. Source: Section 11, `geometry:initial-stars`,
lines 361–370, and `prop:two-families`, lines 313–323. -/
theorem initialRegion_sector_assignment_changes_even
    (o : ℝ × ℝ) (k₀ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (h : ℕ) → Fin (2 ^ (pitchScaleIndex h - fineScaleIndex h)))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (k : ℕ) (z : ℤ × ℤ) (v : ℝ × ℝ) (hk₀ : k₀ ≤ k)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (hv : v ∈ beltCellMarks o (fineScaleIndex k) z) :
    let J := CellFanSlot (fun _ : Fin 4 ↦ true)
    let σ := Classical.choose
      (exists_unique_initialRegion_sector_assignment
        o k₀ Z C a b hC h₀ k z v hk₀ hz hv)
    Even (Nat.card {s : J // σ s ≠ σ (cellFanNext s)}) := by
  classical
  dsimp only
  let σ := Classical.choose
    (exists_unique_initialRegion_sector_assignment
      o k₀ Z C a b hC h₀ k z v hk₀ hz hv)
  have hchange (s : CellFanSlot (fun _ : Fin 4 ↦ true)) :
      σ s ≠ σ (cellFanNext s) ↔
        initialRegionColor o k₀ Z C a b hC h₀ (σ s) ≠
          initialRegionColor o k₀ Z C a b hC h₀ (σ (cellFanNext s)) :=
    not_congr (initialRegion_sector_assignment_adjacent_colors_eq_iff
      o k₀ Z C a b hC h₀ k z v hk₀ hz hv s (cellFanNext s)
      (Or.inl (cellFanEnd_eq_cellFanStart_next _ _ _ s))).symm
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simpa only [← hchange] using
    binaryPermutation_changes_even cellFanNext
      (fun s ↦ initialRegionColor o k₀ Z C a b hC h₀ (σ s))

end TNLean.PEPS.AreaLaw.Geometry

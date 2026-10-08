/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.ElementarySideOpponentUniqueness
import TNLean.PEPS.AreaLaw.Geometry.ActualSideMatching

/-!
# Reciprocal opponents of elementary sides

For dilation width at least two, consider an actual reference fine cell at an
index at least the initial layer index and at least 50,000,000. Each elementary
side has a unique opposing region: the initial dummy neighborhood or an actual
distinct fine cell. An actual candidate fine cell at or above the initial
layer index is its opponent exactly when it is distinct from the reference
and has positive-length contact with the elementary side.
When the initial layer also has index at least 50,000,000, the elementary
segments of the two cells match with reversed endpoints, and each selects the
other as its opponent. These geometric statements provide the consistency needed to assign
opposite labels across an interface; no labels are assigned here.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `prop:two-families`, lines 299–323.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

private theorem segment_contact_of_marks (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    {a b : ℝ × ℝ} (ha : a ∈ beltCellMarks o ℓ z) (hb : b ∈ beltCellMarks o ℓ z)
    (hne : a ≠ b) : segment ℝ a b ⊆ closure (dyadicCell o ℓ z) ∧
      (segment ℝ a b ∩ closure (dyadicCell o ℓ z)).Nontrivial := by
  have hconvex : Convex ℝ (closure (dyadicCell o ℓ z)) := by
    rw [closure_dyadicCell]
    exact (convex_Icc _ _).prod (convex_Icc _ _)
  have hsub := hconvex.segment_subset
    (beltCellMarks_subset_closure_dyadicCell o ℓ z ha)
    (beltCellMarks_subset_closure_dyadicCell o ℓ z hb)
  exact ⟨hsub, (Set.nontrivial_of_mem_mem_ne (left_mem_segment ℝ _ _)
    (right_mem_segment ℝ _ _) hne).mono (fun _ hx ↦ ⟨hx, hsub hx⟩)⟩

/-- The unique actual opposing region, with `none` denoting the dummy region.
Source: area-law Section 11, `prop:two-families`, lines 299–316. -/
def elementarySideOpponent (o : ℝ × ℝ) (k₀ k : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (z : ℤ × ℤ)
    (i : CellFanSlot (fineLayerSplitMask o k₀ k Z C z))
    (hC : 2 ≤ C) (hk : 50000000 ≤ k) (hk₀ : k₀ ≤ k)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C) :
    Option (ℕ × (ℤ × ℤ)) :=
  Classical.choose (exists_unique_elementarySide_opponent o k₀ k Z C z i
    hC hk hk₀ hz).exists

/-- A given actual fine cell is the selected opponent exactly when it is
distinct from the reference and has positive-length contact with its side.
Source: area-law Section 11, `prop:two-families`, lines 299–316. -/
theorem elementarySideOpponent_eq_some_iff_contact (o : ℝ × ℝ) (k₀ k h : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (z w : ℤ × ℤ)
    (i : CellFanSlot (fineLayerSplitMask o k₀ k Z C z))
    (hC : 2 ≤ C) (hk : 50000000 ≤ k) (hk₀ : k₀ ≤ k) (hh₀ : k₀ ≤ h)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (hw : w ∈ fineLayerIndices o h (fineScaleIndex h) Z C) :
    elementarySideOpponent o k₀ k Z C z i hC hk hk₀ hz = some (h, w) ↔
      (k, z) ≠ (h, w) ∧ (segment ℝ
        (cellFanStart o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i)
        (cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i) ∩
        closure (dyadicCell o (fineScaleIndex h) w)).Nontrivial := by
  constructor
  · intro he
    have hspec := Classical.choose_spec
      (exists_unique_elementarySide_opponent o k₀ k Z C z i hC hk hk₀ hz).exists
    rw [show Classical.choose
      (exists_unique_elementarySide_opponent o k₀ k Z C z i hC hk hk₀ hz).exists =
        some (h, w) from he] at hspec
    exact ⟨hspec.2.2.1,
      (Set.nontrivial_of_mem_mem_ne (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
        (cellFan_elementary_geometry o (fineScaleIndex k) z
          (fineLayerSplitMask o k₀ k Z C z) i).1).mono
        (fun _ hx ↦ ⟨hx, hspec.2.2.2 hx⟩)⟩
  · rintro ⟨hne, hcontact⟩
    obtain ⟨j, _, ha, hb⟩ := fineLayer_elementary_contact_match o k₀ k h Z C z w
      hC hk hk₀ hh₀ hz hw hne i hcontact
    exact (exists_unique_elementarySide_opponent o k₀ k Z C z i hC hk hk₀ hz).unique
      (Classical.choose_spec
        (exists_unique_elementarySide_opponent o k₀ k Z C z i hC hk hk₀ hz).exists)
      ⟨hh₀, hw, hne, (segment_contact_of_marks o (fineScaleIndex h) w
        (ha.symm ▸ (cellFan_vertices_mem_beltCellMarks o (fineScaleIndex h) w
          (fineLayerSplitMask o k₀ h Z C w)).2 j |>.2)
        (hb.symm ▸ (cellFan_vertices_mem_beltCellMarks o (fineScaleIndex h) w
          (fineLayerSplitMask o k₀ h Z C w)).2 j |>.1)
        (cellFan_elementary_geometry o (fineScaleIndex k) z
          (fineLayerSplitMask o k₀ k Z C z) i).1).1⟩

/-- A candidate cell is the selected opponent exactly when one of its actual
slots matches the reference slot with reversed endpoints and selects the
reference cell in return. No matching or reciprocity is assumed.
Source: area-law Section 11, `prop:two-families`, lines 299–323. -/
theorem elementarySideOpponent_reciprocal_iff (o : ℝ × ℝ) (k₀ k h : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (z w : ℤ × ℤ)
    (i : CellFanSlot (fineLayerSplitMask o k₀ k Z C z))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (hk₀ : k₀ ≤ k) (hh₀ : k₀ ≤ h)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (hw : w ∈ fineLayerIndices o h (fineScaleIndex h) Z C) :
    elementarySideOpponent o k₀ k Z C z i hC (h₀.trans hk₀) hk₀ hz = some (h, w) ↔
      (k, z) ≠ (h, w) ∧
      ∃ j : CellFanSlot (fineLayerSplitMask o k₀ h Z C w),
        j.1 = i.1 + 2 ∧
        cellFanStart o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i =
          cellFanEnd o (fineScaleIndex h) w (fineLayerSplitMask o k₀ h Z C w) j ∧
        cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i =
          cellFanStart o (fineScaleIndex h) w (fineLayerSplitMask o k₀ h Z C w) j ∧
        elementarySideOpponent o k₀ h Z C w j hC (h₀.trans hh₀) hh₀ hw = some (k, z) := by
  constructor
  · intro he
    obtain ⟨hne, hcontact⟩ := (elementarySideOpponent_eq_some_iff_contact
      o k₀ k h Z C z w i hC (h₀.trans hk₀) hk₀ hh₀ hz hw).mp he
    obtain ⟨j, hj, ha, hb⟩ := fineLayer_elementary_contact_match o k₀ k h Z C z w
      hC (h₀.trans hk₀) hk₀ hh₀ hz hw hne i hcontact
    exact ⟨hne, j, hj, ha, hb,
      (elementarySideOpponent_eq_some_iff_contact o k₀ h k Z C w z j
        hC (h₀.trans hh₀) hh₀ hk₀ hw hz).mpr ⟨hne.symm,
          (segment_contact_of_marks o (fineScaleIndex k) z
            (hb ▸ (cellFan_vertices_mem_beltCellMarks o (fineScaleIndex k) z
              (fineLayerSplitMask o k₀ k Z C z)).2 i |>.2)
            (ha ▸ (cellFan_vertices_mem_beltCellMarks o (fineScaleIndex k) z
              (fineLayerSplitMask o k₀ k Z C z)).2 i |>.1)
            (cellFan_elementary_geometry o (fineScaleIndex h) w
              (fineLayerSplitMask o k₀ h Z C w) j).1).2⟩⟩
  · rintro ⟨hne, j, _, ha, hb, _⟩
    exact (elementarySideOpponent_eq_some_iff_contact o k₀ k h Z C z w i
      hC (h₀.trans hk₀) hk₀ hh₀ hz hw).mpr ⟨hne,
        (segment_contact_of_marks o (fineScaleIndex h) w
          (ha.symm ▸ (cellFan_vertices_mem_beltCellMarks o (fineScaleIndex h) w
            (fineLayerSplitMask o k₀ h Z C w)).2 j |>.2)
          (hb.symm ▸ (cellFan_vertices_mem_beltCellMarks o (fineScaleIndex h) w
            (fineLayerSplitMask o k₀ h Z C w)).2 j |>.1)
          (cellFan_elementary_geometry o (fineScaleIndex k) z
            (fineLayerSplitMask o k₀ k Z C z) i).1).2⟩

end TNLean.PEPS.AreaLaw.Geometry

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.ElementarySideReciprocity
import TNLean.PEPS.AreaLaw.Geometry.NonbeltPrimaries
import Mathlib.Data.Prod.Lex

/-!
# Colors of actual belt-cell fans

Fix an initial layer index at least 50,000,000, dilation width at least two,
and arbitrary choices of the two belt residues at every layer. The triangle
facing the dummy neighborhood receives the opposite dummy parity. The
triangle facing a non-belt fine cell receives the opposite parity of that
cell's primary layer. Across two belt cells, the lexicographic order of their
layer and signed cell indices fixes an opposite pair of colors. This choice
works for every positive-length contact between their elementary sides.

The primary identifier retains both its layer and its pitch-square index,
including when its region is disconnected. Equal-colored runs may subsequently
be formed by the existing connected components of each fan.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `prop:two-families`, lines 172–174,
212–218 and 299–323.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

open scoped Fin.NatCast

namespace TNLean.PEPS.AreaLaw.Geometry

private def cellKey (k : ℕ) (z : ℤ × ℤ) : Lex (ℕ × Lex (ℤ × ℤ)) :=
  toLex (k, toLex z)

private theorem elementary_subset_closed (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (i : CellFanSlot split) :
    segment ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i) ⊆
      closure (dyadicCell o ℓ z) := by
  have htriangle : segment ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i) ⊆
      (cellFanPolygon o ℓ z split i).region :=
    (convexHull_pair (𝕜 := ℝ) (cellFanStart o ℓ z split i)
      (cellFanEnd o ℓ z split i)) ▸
      convexHull_mono (Set.subset_insert (cellFanCenter o ℓ z)
        {cellFanStart o ℓ z split i, cellFanEnd o ℓ z split i})
  exact fun x hx ↦ (cellFanPolygons_cover o ℓ z split) ▸
    (Set.mem_iUnion.mpr ⟨i, htriangle hx⟩)

private theorem opponent_spec (o : ℝ × ℝ) (k₀ k : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (z : ℤ × ℤ)
    (i : CellFanSlot (fineLayerSplitMask o k₀ k Z C z))
    (hC : 2 ≤ C) (hk : 50000000 ≤ k) (hk₀ : k₀ ≤ k)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C) :
    match elementarySideOpponent o k₀ k Z C z i hC hk hk₀ hz with
    | none => segment ℝ
        (cellFanStart o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i)
        (cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i) ⊆
          closure (dyadicNeighborhood o k₀ Z C)
    | some (h, w) => k₀ ≤ h ∧ w ∈ fineLayerIndices o h (fineScaleIndex h) Z C ∧
        (k, z) ≠ (h, w) ∧ segment ℝ
        (cellFanStart o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i)
        (cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i) ⊆
          closure (dyadicCell o (fineScaleIndex h) w) := by
  exact Classical.choose_spec
    (exists_unique_elementarySide_opponent o k₀ k Z C z i hC hk hk₀ hz).exists

private theorem opposite_ne (c : Fin 2) : c + 1 ≠ c := by
  exact fun h ↦ (by decide : (1 : Fin 2) ≠ 0)
    (add_left_cancel (h.trans (add_zero c).symm))

/-- The actual fan color determined by the unique opposing region: the opposite
primary or dummy parity, or the ordered opposite pair for two belt cells.
Source: area-law Section 11, `prop:two-families`, lines 172–174, 212–218 and 299–316. -/
def beltCellFanColor (o : ℝ × ℝ) (k₀ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (h : ℕ) → Fin (2 ^ (pitchScaleIndex h - fineScaleIndex h)))
    (k : ℕ) (z : ℤ × ℤ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (hk₀ : k₀ ≤ k)
    (hz : z ∈ beltCellIndices (fineLayerIndices o k (fineScaleIndex k) Z C)
      (2 ^ (pitchScaleIndex k - fineScaleIndex k)) (a k) (b k)) :
    CellFanSlot (fineLayerSplitMask o k₀ k Z C z) → Fin 2 := fun i ↦
  match elementarySideOpponent o k₀ k Z C z i hC (h₀.trans hk₀) hk₀
      (Finset.mem_of_mem_filter z hz) with
  | none => ((k₀ - 1 : ℕ) : Fin 2) + 1
  | some (h, w) =>
    if w ∈ beltCellIndices (fineLayerIndices o h (fineScaleIndex h) Z C)
        (2 ^ (pitchScaleIndex h - fineScaleIndex h)) (a h) (b h) then
      if cellKey k z < cellKey h w then 0 else 1
    else (h : Fin 2) + 1

/-- A fan side contained in the actual dummy closure receives the opposite dummy label.
Source: area-law Section 11, `prop:two-families`, lines 172–174 and 299–316. -/
theorem beltCellFanColor_dummy (o : ℝ × ℝ) (k₀ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (h : ℕ) → Fin (2 ^ (pitchScaleIndex h - fineScaleIndex h)))
    (k : ℕ) (z : ℤ × ℤ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (hk₀ : k₀ ≤ k)
    (hz : z ∈ beltCellIndices (fineLayerIndices o k (fineScaleIndex k) Z C)
      (2 ^ (pitchScaleIndex k - fineScaleIndex k)) (a k) (b k))
    (i : CellFanSlot (fineLayerSplitMask o k₀ k Z C z))
    (hN : segment ℝ
      (cellFanStart o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i)
      (cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i) ⊆
        closure (dyadicNeighborhood o k₀ Z C)) :
    beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz i = ((k₀ - 1 : ℕ) : Fin 2) + 1 ∧
      beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz i ≠ ((k₀ - 1 : ℕ) : Fin 2) := by
  have he : elementarySideOpponent o k₀ k Z C z i hC (h₀.trans hk₀) hk₀
      (Finset.mem_of_mem_filter z hz) = none :=
    (exists_unique_elementarySide_opponent o k₀ k Z C z i hC (h₀.trans hk₀) hk₀
      (Finset.mem_of_mem_filter z hz)).unique
        (opponent_spec o k₀ k Z C z i hC (h₀.trans hk₀) hk₀
          (Finset.mem_of_mem_filter z hz)) hN
  exact ⟨by simp [beltCellFanColor, he],
    by simpa only [beltCellFanColor, he] using opposite_ne ((k₀ - 1 : ℕ) : Fin 2)⟩

/-- Positive contact with an actual non-belt cell identifies its retained primary,
contains the whole fan side in that primary birth region, and gives the opposite label.
Source: area-law Section 11, `prop:two-families`, lines 212–218 and 299–316. -/
theorem beltCellFanColor_nonbelt_opponent (o : ℝ × ℝ) (k₀ : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (h : ℕ) → Fin (2 ^ (pitchScaleIndex h - fineScaleIndex h)))
    (k h : ℕ) (z w : ℤ × ℤ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (hk₀ : k₀ ≤ k) (hh₀ : k₀ ≤ h)
    (hz : z ∈ beltCellIndices (fineLayerIndices o k (fineScaleIndex k) Z C)
      (2 ^ (pitchScaleIndex k - fineScaleIndex k)) (a k) (b k))
    (hw : w ∈ fineLayerIndices o h (fineScaleIndex h) Z C)
    (hnot : w ∉ beltCellIndices (fineLayerIndices o h (fineScaleIndex h) Z C)
      (2 ^ (pitchScaleIndex h - fineScaleIndex h)) (a h) (b h))
    (i : CellFanSlot (fineLayerSplitMask o k₀ k Z C z))
    (hcontact : (segment ℝ
      (cellFanStart o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i)
      (cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i) ∩
      closure (dyadicCell o (fineScaleIndex h) w)).Nontrivial) :
    let J := nonbeltPitchIndex (fineScaleIndex h) (pitchScaleIndex h) (a h).val (b h).val w
    J ∈ primaryPitchIndices o h (fineScaleIndex h) (pitchScaleIndex h) Z C
        (a h).val (b h).val ∧
      segment ℝ
        (cellFanStart o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i)
        (cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i) ⊆
          primaryBirthRegion o h (fineScaleIndex h) (pitchScaleIndex h) Z C
            (a h).val (b h).val J ∧
      beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz i = (h : Fin 2) + 1 ∧
      beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz i ≠ (h : Fin 2) := by
  have hne : (k, z) ≠ (h, w) := by
    intro he
    cases he
    exact hnot hz
  have he := (elementarySideOpponent_eq_some_iff_contact o k₀ k h Z C z w i
    hC (h₀.trans hk₀) hk₀ hh₀ (Finset.mem_of_mem_filter z hz) hw).mpr ⟨hne, hcontact⟩
  have hsub := (he ▸ opponent_spec o k₀ k Z C z i hC (h₀.trans hk₀) hk₀
    (Finset.mem_of_mem_filter z hz)).2.2.2
  have hprimary := hsub.trans (closure_nonbeltCell_subset_primaryBirthRegion o h
    (fineScaleIndex h) (pitchScaleIndex h) Z C (a h) (b h) w (fineScaleIndex_le h)
    ((fineScaleIndex_le h).trans (le_pitchScaleIndex h)) hw hnot)
  have hret := (mem_primaryPitchIndices_iff o h (fineScaleIndex h) (pitchScaleIndex h)
    Z C (a h).val (b h).val
    (nonbeltPitchIndex (fineScaleIndex h) (pitchScaleIndex h) (a h).val (b h).val w)).mpr
      (Set.Nonempty.of_closure ⟨_, hprimary (left_mem_segment ℝ _ _)⟩)
  have hc : beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz i = (h : Fin 2) + 1 := by
    simp [beltCellFanColor, he, hnot]
  exact ⟨hret, hprimary, hc, hc.symm ▸ opposite_ne (h : Fin 2)⟩

/-- Every positive-length contact between two actual belt-cell fan sides has opposite
colors, without selecting an opposing slot as a hypothesis.
Source: area-law Section 11, `prop:two-families`, lines 299–323. -/
theorem beltCellFanColor_belt_contact (o : ℝ × ℝ) (k₀ : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (h : ℕ) → Fin (2 ^ (pitchScaleIndex h - fineScaleIndex h)))
    (k h : ℕ) (z w : ℤ × ℤ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (hk₀ : k₀ ≤ k) (hh₀ : k₀ ≤ h)
    (hz : z ∈ beltCellIndices (fineLayerIndices o k (fineScaleIndex k) Z C)
      (2 ^ (pitchScaleIndex k - fineScaleIndex k)) (a k) (b k))
    (hw : w ∈ beltCellIndices (fineLayerIndices o h (fineScaleIndex h) Z C)
      (2 ^ (pitchScaleIndex h - fineScaleIndex h)) (a h) (b h))
    (hne : (k, z) ≠ (h, w))
    (i : CellFanSlot (fineLayerSplitMask o k₀ k Z C z))
    (j : CellFanSlot (fineLayerSplitMask o k₀ h Z C w))
    (hcontact : (segment ℝ
      (cellFanStart o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i)
      (cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i) ∩
      segment ℝ
        (cellFanStart o (fineScaleIndex h) w (fineLayerSplitMask o k₀ h Z C w) j)
        (cellFanEnd o (fineScaleIndex h) w (fineLayerSplitMask o k₀ h Z C w) j)).Nontrivial) :
    beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz i ≠
      beltCellFanColor o k₀ Z C a b h w hC h₀ hh₀ hw j := by
  have hzfine := Finset.mem_of_mem_filter z hz
  have he := (elementarySideOpponent_eq_some_iff_contact o k₀ k h Z C z w i
    hC (h₀.trans hk₀) hk₀ hh₀ hzfine (Finset.mem_of_mem_filter w hw)).mpr
      ⟨hne, hcontact.mono (fun _ hx ↦ ⟨hx.1, elementary_subset_closed o
        (fineScaleIndex h) w (fineLayerSplitMask o k₀ h Z C w) j hx.2⟩)⟩
  have he' := (elementarySideOpponent_eq_some_iff_contact o k₀ h k Z C w z j
    hC (h₀.trans hh₀) hh₀ hk₀ (Finset.mem_of_mem_filter w hw) hzfine).mpr
      ⟨hne.symm, hcontact.mono (fun _ hx ↦ ⟨hx.2, elementary_subset_closed o
        (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i hx.1⟩)⟩
  have hkey : cellKey k z ≠ cellKey h w := by
    simpa only [Ne, cellKey, toLex_inj, Prod.mk.injEq] using hne
  rcases lt_or_gt_of_ne hkey with hlt | hlt
  all_goals simp [beltCellFanColor, he, he', hz, hw, hlt, not_lt_of_ge hlt.le]

end TNLean.PEPS.AreaLaw.Geometry

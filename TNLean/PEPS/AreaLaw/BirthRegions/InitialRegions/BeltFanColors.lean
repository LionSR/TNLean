/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.BirthRegions.Fans.ElementarySideReciprocity
import TNLean.PEPS.AreaLaw.BirthRegions.Layers.NonbeltPrimaries
import Mathlib.Order.Prod.Lex.Basic
import TNLean.PEPS.AreaLaw.BirthRegions.Fans.FanRuns
import TNLean.PEPS.AreaLaw.BirthRegions.Fans.FanSideContacts
import TNLean.PEPS.AreaLaw.BirthRegions.InitialRegions.PrimaryFineCellCover
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Interval.Set.Infinite
import TNLean.PEPS.AreaLaw.BirthRegions.Fans.CellContacts
import Mathlib.Topology.Order.DenselyOrdered

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

It also contains the following results.

* `TNLean.PEPS.AreaLaw.Geometry.beltCellFanRun_primary_interface`,
  `TNLean.PEPS.AreaLaw.Geometry.beltCellFanRuns_interface_colors_ne`: positive-length interfaces of
  actual belt runs.
* `TNLean.PEPS.AreaLaw.Geometry.fineLayer_cellFanPolygon_inter_dummy_eq`,
  `TNLean.PEPS.AreaLaw.Geometry.beltCellFanRun_dummy_interface`: dummy interfaces of actual belt
  runs.
-/

section BeltFanColors

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

end

end BeltFanColors

section BeltRunInterfaces

/-!
## Positive-length interfaces of actual belt runs

A closed segment with distinct endpoints shared by an actual belt run and
a primary birth region identifies a retained primary and forces every
triangle of the run to have the opposite primary parity. A segment shared
by runs in distinct actual belt cells forces all their constituent colors
to differ. Arbitrary belt residue functions are allowed.

The shared segment is covered by finitely many actual triangle and cell
intersections. Infinitude extracts a two-point constituent contact. The
triangle face equalities reduce it to elementary-base contact, and the
existing local color rules and run color constancy give the conclusions.
Two isolated common corners are not substituted for a shared segment.

Source: OpenAI, A two-dimensional area law from a global spectral gap,
September 24, 2026, Section 11, prop:two-families, lines 212–218 and 299–323.
Source revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

open scoped Fin.NatCast

namespace TNLean.PEPS.AreaLaw.Geometry

private theorem exists_nontrivial_inter_of_infinite_cover
    {X I : Type*} [Finite I] {S : Set X} {A : I → Set X}
    (hS : S.Infinite) (hcover : S ⊆ ⋃ i, A i) :
    ∃ i, (S ∩ A i).Nontrivial := by
  classical
  exact Classical.byContradiction fun hn ↦ hS
    ((Set.finite_iUnion fun i ↦
      (Set.not_nontrivial_iff.mp (not_exists.mp hn i)).finite).subset fun x hx ↦
        let ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hx)
        Set.mem_iUnion.mpr ⟨i, hx, hi⟩)

private theorem segment_infinite {u v : ℝ × ℝ} (huv : u ≠ v) :
    (segment ℝ u v).Infinite := by
  rw [segment_eq_image_lineMap]
  exact (Set.Icc_infinite (by norm_num : (0 : ℝ) < 1)).image
    (AffineMap.lineMap_injective ℝ huv).injOn

/-- A shared nondegenerate segment with an actual primary birth region derives
its retained index and the opposite primary parity for every triangle of the run.
Source: area-law Section 11, prop:two-families, lines 212–218 and 299–323. -/
theorem beltCellFanRun_primary_interface
    (o : ℝ × ℝ) (k₀ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (h : ℕ) → Fin (2 ^ (pitchScaleIndex h - fineScaleIndex h)))
    (k h : ℕ) (z J : ℤ × ℤ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (hk₀ : k₀ ≤ k) (hh₀ : k₀ ≤ h)
    (hz : z ∈ beltCellIndices (fineLayerIndices o k (fineScaleIndex k) Z C)
      (2 ^ (pitchScaleIndex k - fineScaleIndex k)) (a k) (b k))
    (R : CellFanRun o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z)
      (beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz))
    (u v : ℝ × ℝ) (huv : u ≠ v)
    (hsegment : segment ℝ u v ⊆
      cellFanRunRegion o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z)
        (beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz) R ∩
      primaryBirthRegion o h (fineScaleIndex h) (pitchScaleIndex h) Z C
        (a h).val (b h).val J) :
    J ∈ primaryPitchIndices o h (fineScaleIndex h) (pitchScaleIndex h) Z C
        (a h).val (b h).val ∧
      ∀ i ∈ R.supp, beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz i =
          (h : Fin 2) + 1 ∧
        beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz i ≠ (h : Fin 2) := by
  classical
  let T := (fineLayerIndices o h (fineScaleIndex h) Z C).filter (fun w ↦
    w ∉ beltCellIndices (fineLayerIndices o h (fineScaleIndex h) Z C)
      (2 ^ (pitchScaleIndex h - fineScaleIndex h)) (a h) (b h) ∧
      nonbeltPitchIndex (fineScaleIndex h) (pitchScaleIndex h) (a h).val (b h).val w = J)
  have hprimary : primaryBirthRegion o h (fineScaleIndex h) (pitchScaleIndex h)
      Z C (a h).val (b h).val J =
      ⋃ w ∈ T, closure (dyadicCell o (fineScaleIndex h) w) :=
    primaryBirthRegion_eq_iUnion_nonbeltCell_closure o h (fineScaleIndex h)
      (pitchScaleIndex h) Z C (a h) (b h) J (fineScaleIndex_le h)
      ((fineScaleIndex_le h).trans (le_pitchScaleIndex h))
  have hcover : segment ℝ u v ⊆
      ⋃ q : {i : CellFanSlot (fineLayerSplitMask o k₀ k Z C z) // i ∈ R.supp} ×
        {w : ℤ × ℤ // w ∈ T},
        (cellFanPolygon o (fineScaleIndex k) z
          (fineLayerSplitMask o k₀ k Z C z) q.1.val).region ∩
          closure (dyadicCell o (fineScaleIndex h) q.2.val) := by
    intro x hx
    have hxR := (hsegment hx).1
    have hxP := (hsegment hx).2
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hxR
    rw [hprimary] at hxP
    obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hxP
    exact Set.mem_iUnion.mpr ⟨(⟨i, hi⟩, ⟨w, hw⟩), hxi, hxw⟩
  obtain ⟨q, hcontact⟩ :=
    exists_nontrivial_inter_of_infinite_cover (segment_infinite huv) hcover
  rcases q with ⟨⟨i, hi⟩, ⟨w, hw⟩⟩
  have htriangle : ((cellFanPolygon o (fineScaleIndex k) z
      (fineLayerSplitMask o k₀ k Z C z) i).region ∩
      closure (dyadicCell o (fineScaleIndex h) w)).Nontrivial :=
    hcontact.mono (fun _ hx ↦ hx.2)
  obtain ⟨hwfine, hwnot, hindex⟩ := Finset.mem_filter.mp hw
  have hne : (k, z) ≠ (h, w) := by
    intro he
    cases he
    exact hwnot hz
  rw [fineLayer_cellFanPolygon_inter_closedCell_eq o k h Z C z w
    (fineLayerSplitMask o k₀ k Z C z) i (Finset.mem_of_mem_filter z hz)
    hwfine hne] at htriangle
  have hlocal := beltCellFanColor_nonbelt_opponent o k₀ Z C a b k h z w
    hC h₀ hk₀ hh₀ hz hwfine hwnot i htriangle
  refine ⟨by simpa only [hindex] using hlocal.1, ?_⟩
  intro j hj
  have hsame := cellFanRun_color_eq o (fineScaleIndex k) z
    (fineLayerSplitMask o k₀ k Z C z)
    (beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz) j i
    (SimpleGraph.ConnectedComponent.eq.mpr (R.reachable_of_mem_supp hj hi))
  exact ⟨hsame.trans hlocal.2.2.1, hsame.symm ▸ hlocal.2.2.2⟩

/-- A shared nondegenerate segment between actual runs in distinct indexed belt
cells forces every constituent color of one run to differ from every color of the other.
Source: area-law Section 11, prop:two-families, lines 299–323. -/
theorem beltCellFanRuns_interface_colors_ne
    (o : ℝ × ℝ) (k₀ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (h : ℕ) → Fin (2 ^ (pitchScaleIndex h - fineScaleIndex h)))
    (k h : ℕ) (z w : ℤ × ℤ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (hk₀ : k₀ ≤ k) (hh₀ : k₀ ≤ h)
    (hz : z ∈ beltCellIndices (fineLayerIndices o k (fineScaleIndex k) Z C)
      (2 ^ (pitchScaleIndex k - fineScaleIndex k)) (a k) (b k))
    (hw : w ∈ beltCellIndices (fineLayerIndices o h (fineScaleIndex h) Z C)
      (2 ^ (pitchScaleIndex h - fineScaleIndex h)) (a h) (b h))
    (R : CellFanRun o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z)
      (beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz))
    (T : CellFanRun o (fineScaleIndex h) w (fineLayerSplitMask o k₀ h Z C w)
      (beltCellFanColor o k₀ Z C a b h w hC h₀ hh₀ hw))
    (hne : (k, z) ≠ (h, w)) (u v : ℝ × ℝ) (huv : u ≠ v)
    (hsegment : segment ℝ u v ⊆
      cellFanRunRegion o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z)
        (beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz) R ∩
      cellFanRunRegion o (fineScaleIndex h) w (fineLayerSplitMask o k₀ h Z C w)
        (beltCellFanColor o k₀ Z C a b h w hC h₀ hh₀ hw) T) :
    ∀ i ∈ R.supp, ∀ j ∈ T.supp,
      beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz i ≠
        beltCellFanColor o k₀ Z C a b h w hC h₀ hh₀ hw j := by
  classical
  have hcover : segment ℝ u v ⊆
      ⋃ q : {i : CellFanSlot (fineLayerSplitMask o k₀ k Z C z) // i ∈ R.supp} ×
        {j : CellFanSlot (fineLayerSplitMask o k₀ h Z C w) // j ∈ T.supp},
        (cellFanPolygon o (fineScaleIndex k) z
          (fineLayerSplitMask o k₀ k Z C z) q.1.val).region ∩
        (cellFanPolygon o (fineScaleIndex h) w
          (fineLayerSplitMask o k₀ h Z C w) q.2.val).region := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hsegment hx).1
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp (hsegment hx).2
    exact Set.mem_iUnion.mpr ⟨(⟨i, hi⟩, ⟨j, hj⟩), hxi, hxj⟩
  obtain ⟨q, hcontact⟩ :=
    exists_nontrivial_inter_of_infinite_cover (segment_infinite huv) hcover
  rcases q with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  have htriangles : ((cellFanPolygon o (fineScaleIndex k) z
      (fineLayerSplitMask o k₀ k Z C z) i).region ∩
      (cellFanPolygon o (fineScaleIndex h) w
        (fineLayerSplitMask o k₀ h Z C w) j).region).Nontrivial :=
    hcontact.mono (fun _ hx ↦ hx.2)
  have hi_eq := fineLayer_cellFanPolygon_inter_closedCell_eq o k h Z C z w
    (fineLayerSplitMask o k₀ k Z C z) i (Finset.mem_of_mem_filter z hz)
    (Finset.mem_of_mem_filter w hw) hne
  have hj_eq := fineLayer_cellFanPolygon_inter_closedCell_eq o h k Z C w z
    (fineLayerSplitMask o k₀ h Z C w) j (Finset.mem_of_mem_filter w hw)
    (Finset.mem_of_mem_filter z hz) hne.symm
  have hbases : (segment ℝ
      (cellFanStart o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i)
      (cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i) ∩
      segment ℝ
        (cellFanStart o (fineScaleIndex h) w (fineLayerSplitMask o k₀ h Z C w) j)
        (cellFanEnd o (fineScaleIndex h) w (fineLayerSplitMask o k₀ h Z C w) j)).Nontrivial :=
    htriangles.mono fun x hx ↦ by
      have hclosed_z : x ∈ closure (dyadicCell o (fineScaleIndex k) z) :=
        (cellFanPolygons_cover o (fineScaleIndex k) z
          (fineLayerSplitMask o k₀ k Z C z)) ▸ Set.mem_iUnion.mpr ⟨i, hx.1⟩
      have hclosed_w : x ∈ closure (dyadicCell o (fineScaleIndex h) w) :=
        (cellFanPolygons_cover o (fineScaleIndex h) w
          (fineLayerSplitMask o k₀ h Z C w)) ▸ Set.mem_iUnion.mpr ⟨j, hx.2⟩
      exact ⟨((Set.ext_iff.mp hi_eq x).mp ⟨hx.1, hclosed_w⟩).1,
        ((Set.ext_iff.mp hj_eq x).mp ⟨hx.2, hclosed_z⟩).1⟩
  have hcolors := beltCellFanColor_belt_contact o k₀ Z C a b k h z w
    hC h₀ hk₀ hh₀ hz hw hne i j hbases
  intro i' hi' j' hj'
  have hsameR := cellFanRun_color_eq o (fineScaleIndex k) z
    (fineLayerSplitMask o k₀ k Z C z)
    (beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz) i' i
    (SimpleGraph.ConnectedComponent.eq.mpr (R.reachable_of_mem_supp hi' hi))
  have hsameT := cellFanRun_color_eq o (fineScaleIndex h) w
    (fineLayerSplitMask o k₀ h Z C w)
    (beltCellFanColor o k₀ Z C a b h w hC h₀ hh₀ hw) j' j
    (SimpleGraph.ConnectedComponent.eq.mpr (T.reachable_of_mem_supp hj' hj))
  simpa only [hsameR, hsameT] using hcolors

end TNLean.PEPS.AreaLaw.Geometry

end BeltRunInterfaces

section DummyRunInterfaces

/-!
## Dummy interfaces of actual belt runs

A fan triangle of an actual fine cell meets the closed initial dummy
neighborhood precisely through its elementary base. This identity holds
for every neighborhood width and optional midpoint subdivision, including
empty and single-point contacts. Actual layer disjointness puts each
contact on a whole square side, where the established own-side identity
reduces the contact to the base.

If an actual belt run and the dummy closure share a nondegenerate segment,
every constituent triangle of the run has the opposite dummy parity.
The shared segment supplies a contact away from the finite set of elementary
endpoints. The open-side continuation theorem extends that contact to the
whole base, and the local color rule and run constancy give the conclusion.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `prop:two-families`, lines 154–177 and 299–323.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

open scoped Fin.NatCast

namespace TNLean.PEPS.AreaLaw.Geometry

/-- A fan triangle of an actual later fine cell meets the dummy closure exactly
where its elementary base does. The neighborhood width and optional midpoint
subdivision are arbitrary, and empty or singleton contacts are included.
Source: area-law Section 11, `prop:two-families`, lines 154–177 and 299–323. -/
theorem fineLayer_cellFanPolygon_inter_dummy_eq
    (o : ℝ × ℝ) (k₀ k : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (z : ℤ × ℤ) (split : Fin 4 → Bool) (i : CellFanSlot split)
    (hk₀ : k₀ ≤ k)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C) :
    (cellFanPolygon o (fineScaleIndex k) z split i).region ∩
        closure (dyadicNeighborhood o k₀ Z C) =
      segment ℝ (cellFanStart o (fineScaleIndex k) z split i)
          (cellFanEnd o (fineScaleIndex k) z split i) ∩
        closure (dyadicNeighborhood o k₀ Z C) := by
  have href := dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices o k
    (fineScaleIndex k) Z C z (fineScaleIndex_le k) hz
  have hd := (dyadicNeighborhood_disjoint_later_layer o Z C k₀ k hk₀).symm.mono_left href
  have hclosed := (hd.mono_left interior_subset).closure_right isOpen_interior
  apply Set.Subset.antisymm
  · intro x hx
    have hxcell : x ∈ closure (dyadicCell o (fineScaleIndex k) z) :=
      (cellFanPolygons_cover o (fineScaleIndex k) z split) ▸
        Set.mem_iUnion.mpr ⟨i, hx.1⟩
    have hxfront : x ∈ frontier (dyadicCell o (fineScaleIndex k) z) := by
      rw [← closure_sdiff_interior]
      exact ⟨hxcell, fun hi ↦ Set.disjoint_left.mp hclosed hi hx.2⟩
    obtain ⟨s, hs⟩ := exists_dyadicCellSide_of_mem_frontier o (fineScaleIndex k) z x hxfront
    have hface := cellFanPolygon_inter_dyadicCellSide o (fineScaleIndex k) z split i s
    exact ⟨((Set.ext_iff.mp hface x).mp ⟨hx.1, hs⟩).1, hx.2⟩
  · intro x hx
    have hjoin : convexJoin ℝ {cellFanCenter o (fineScaleIndex k) z}
        (segment ℝ (cellFanStart o (fineScaleIndex k) z split i)
          (cellFanEnd o (fineScaleIndex k) z split i)) =
        (cellFanPolygon o (fineScaleIndex k) z split i).region :=
      convexJoin_singleton_segment _ _ _
    exact ⟨hjoin ▸ subset_convexJoin_right (Set.singleton_nonempty _) hx.1, hx.2⟩

/-- A nondegenerate segment shared by an actual belt run and the dummy closure
forces every constituent triangle to have the opposite dummy parity.
Source: area-law Section 11, `prop:two-families`, lines 172–174 and 299–323. -/
theorem beltCellFanRun_dummy_interface
    (o : ℝ × ℝ) (k₀ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (h : ℕ) → Fin (2 ^ (pitchScaleIndex h - fineScaleIndex h)))
    (k : ℕ) (z : ℤ × ℤ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (hk₀ : k₀ ≤ k)
    (hz : z ∈ beltCellIndices (fineLayerIndices o k (fineScaleIndex k) Z C)
      (2 ^ (pitchScaleIndex k - fineScaleIndex k)) (a k) (b k))
    (R : CellFanRun o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z)
      (beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz))
    (u v : ℝ × ℝ) (huv : u ≠ v)
    (hsegment : segment ℝ u v ⊆
      cellFanRunRegion o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z)
        (beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz) R ∩
      closure (dyadicNeighborhood o k₀ Z C)) :
    ∀ i ∈ R.supp, beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz i =
        ((k₀ - 1 : ℕ) : Fin 2) + 1 ∧
      beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz i ≠
        ((k₀ - 1 : ℕ) : Fin 2) := by
  classical
  let split := fineLayerSplitMask o k₀ k Z C z
  let endpoints := ⋃ i : CellFanSlot split,
    ({cellFanStart o (fineScaleIndex k) z split i,
      cellFanEnd o (fineScaleIndex k) z split i} : Set (ℝ × ℝ))
  have hfinite : endpoints.Finite :=
    Set.finite_iUnion fun _ ↦ (Set.finite_singleton _).insert _
  have hinfinite : (segment ℝ u v).Infinite := by
    rw [segment_eq_image_lineMap]
    exact (Set.Icc_infinite (by norm_num : (0 : ℝ) < 1)).image
      (AffineMap.lineMap_injective ℝ huv).injOn
  obtain ⟨x, hxS, hxends⟩ := hinfinite.exists_notMem_finite hfinite
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hsegment hxS).1
  have hxN := (hsegment hxS).2
  have hxbase : x ∈ segment ℝ (cellFanStart o (fineScaleIndex k) z split i)
      (cellFanEnd o (fineScaleIndex k) z split i) := by
    have hface := fineLayer_cellFanPolygon_inter_dummy_eq o k₀ k Z C z split i
      hk₀ (Finset.mem_of_mem_filter z hz)
    exact ((Set.ext_iff.mp hface x).mp ⟨hxi, hxN⟩).1
  have hxne (he : x = cellFanStart o (fineScaleIndex k) z split i ∨
      x = cellFanEnd o (fineScaleIndex k) z split i) : False := by
    apply hxends
    exact Set.mem_iUnion.mpr ⟨i, he⟩
  have hxopen := mem_openSegment_of_ne_left_right
    (fun he ↦ hxne (Or.inl he.symm)) (fun he ↦ hxne (Or.inr he.symm)) hxbase
  have hwhole := fineLayer_elementarySide_subset_dummy_of_mem_openSegment
    o k₀ k Z C z split i x hC hk₀ (Finset.mem_of_mem_filter z hz) hxopen hxN
  have hcolor := beltCellFanColor_dummy o k₀ Z C a b k z hC h₀ hk₀ hz i hwhole
  intro j hj
  have hsame := cellFanRun_color_eq o (fineScaleIndex k) z split
    (beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz) j i
    (SimpleGraph.ConnectedComponent.eq.mpr (R.reachable_of_mem_supp hj hi))
  exact ⟨hsame.trans hcolor.1, hsame.symm ▸ hcolor.2⟩

end TNLean.PEPS.AreaLaw.Geometry

end DummyRunInterfaces

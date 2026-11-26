/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.BirthRegions.Layers.LayerPartition
import TNLean.PEPS.AreaLaw.BirthRegions.Fans.DummyCorners
import TNLean.PEPS.AreaLaw.BirthRegions.Fans.CellContacts
import TNLean.PEPS.AreaLaw.BirthRegions.Fans.SideSubdivision
import Mathlib.Analysis.Convex.Topology
import Mathlib.Order.Interval.Set.Disjoint

/-!
# Opposing regions along actual elementary sides

For dilation width at least two, let an actual reference cell belong to a layer
of index at least 50,000,000 and no smaller than the initial layer index.
Every elementary side of its actual midpoint subdivision faces either the
initial dummy neighborhood or one actual distinct fine cell. That closed region
contains the whole elementary side. Existence follows from the actual plane
cover in an outward neighborhood; actual corner exclusion prevents the contact
from ending inside the elementary side.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, lines 154–181 and 299–310.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.

It also contains the following results.

* `TNLean.PEPS.AreaLaw.Geometry.exists_unique_elementarySide_opponent`: uniqueness of the region
  opposing an elementary side.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

section ElementarySideOpponents

private theorem interval_overlap_of_mem {a b c d x : ℝ}
    (hab : a < b) (hcd : c < d) (hx : x ∈ Set.Icc a b)
    (hy : x ∈ Set.Ioo c d) : max a c < min b d := by
  rw [max_lt_iff, lt_min_iff, lt_min_iff]
  exact ⟨⟨hab, lt_of_le_of_lt hx.1 hy.2⟩,
    ⟨lt_of_lt_of_le hy.1 hx.2, hcd⟩⟩

private theorem rectangle_normal_boundary {p q a b : ℝ × ℝ} {ξ η : ℝ}
    (hp : p.1 < q.1 ∧ p.2 < q.2) (ha : a.1 < b.1 ∧ a.2 < b.2)
    (hξp : ξ ∈ Set.Icc p.1 q.1) (hηp : η ∈ Set.Ioo p.2 q.2)
    (hξa : ξ ∈ Set.Icc a.1 b.1) (hηa : η ∈ Set.Icc a.2 b.2)
    (hdisj : Disjoint (Set.Ioo p.1 q.1 ×ˢ Set.Ioo p.2 q.2)
      (Set.Ioo a.1 b.1 ×ˢ Set.Ioo a.2 b.2)) : ξ = a.1 ∨ ξ = b.1 := by
  by_contra! hne
  have hξ : ξ ∈ Set.Ioo a.1 b.1 :=
    ⟨lt_of_le_of_ne hξa.1 hne.1.symm, lt_of_le_of_ne hξa.2 hne.2⟩
  obtain ⟨u, hu⟩ := Set.nonempty_Ioo.mpr (interval_overlap_of_mem hp.1 ha.1 hξp hξ)
  obtain ⟨v, hv⟩ := Set.nonempty_Ioo.mpr (interval_overlap_of_mem ha.2 hp.2 hηa hηp)
  apply Set.disjoint_left.mp hdisj (show (u, v) ∈ _ from ?_) (show (u, v) ∈ _ from ?_)
  · exact ⟨⟨lt_of_le_of_lt (le_max_left _ _) hu.1,
      lt_of_lt_of_le hu.2 (min_le_left _ _)⟩,
      ⟨lt_of_le_of_lt (le_max_right _ _) hv.1,
        lt_of_lt_of_le hv.2 (min_le_right _ _)⟩⟩
  · exact ⟨⟨lt_of_le_of_lt (le_max_right _ _) hu.1,
      lt_of_lt_of_le hu.2 (min_le_right _ _)⟩,
      ⟨lt_of_le_of_lt (le_max_left _ _) hv.1,
        lt_of_lt_of_le hv.2 (min_le_left _ _)⟩⟩

/-- The corner of the closed axis-parallel rectangle with opposite corners `a`
and `b` selected by `ε`, where the coordinate `0` picks `a` and `1` picks `b`.
Source: area-law Section 11, lines 299–316. -/
def rectangleCorner (a b : ℝ × ℝ) (ε : Fin 2 × Fin 2) : ℝ × ℝ :=
  (if ε.1.val = 0 then a.1 else b.1, if ε.2.val = 0 then a.2 else b.2)

private theorem rectangle_vertical_containment {p q a b : ℝ × ℝ} {ξ η l u : ℝ}
    (hp : p.1 < q.1 ∧ p.2 < q.2) (ha : a.1 < b.1 ∧ a.2 < b.2)
    (hξp : ξ ∈ Set.Icc p.1 q.1) (hl : p.2 ≤ l) (hu : u ≤ q.2)
    (hη : η ∈ Set.Ioo l u)
    (hx : (ξ, η) ∈ Set.Icc a.1 b.1 ×ˢ Set.Icc a.2 b.2)
    (hdisj : Disjoint (Set.Ioo p.1 q.1 ×ˢ Set.Ioo p.2 q.2)
      (Set.Ioo a.1 b.1 ×ˢ Set.Ioo a.2 b.2))
    (hcorners : ∀ ε : Fin 2 × Fin 2,
      rectangleCorner a b ε ∉ {ξ} ×ˢ Set.Ioo l u) :
    {ξ} ×ˢ Set.Icc l u ⊆ Set.Icc a.1 b.1 ×ˢ Set.Icc a.2 b.2 := by
  have hηp : η ∈ Set.Ioo p.2 q.2 := ⟨hl.trans_lt hη.1, hη.2.trans_le hu⟩
  have hξ := rectangle_normal_boundary hp ha hξp hηp hx.1 hx.2 hdisj
  have hlo : a.2 ≤ l := by
    by_contra! h
    have hy : a.2 ∈ Set.Ioo l u := ⟨h, lt_of_le_of_lt hx.2.1 hη.2⟩
    rcases hξ with rfl | rfl
    · exact hcorners (0, 0) (by simpa [rectangleCorner] using hy)
    · exact hcorners (1, 0) (by simpa [rectangleCorner] using hy)
  have hhi : u ≤ b.2 := by
    by_contra! h
    have hy : b.2 ∈ Set.Ioo l u := ⟨lt_of_lt_of_le hη.1 hx.2.2, h⟩
    rcases hξ with rfl | rfl
    · exact hcorners (0, 1) (by simpa [rectangleCorner] using hy)
    · exact hcorners (1, 1) (by simpa [rectangleCorner] using hy)
  intro y hy
  have hyξ : y.1 = ξ := hy.1
  exact ⟨by simpa only [hyξ] using hx.1,
    ⟨hlo.trans hy.2.1, hy.2.2.trans hhi⟩⟩

/-- Coordinates of the midpoint of two points in the plane. -/
theorem midpoint_prod_eq (u v : ℝ × ℝ) :
    midpoint ℝ u v = ((u.1 + v.1) / 2, (u.2 + v.2) / 2) := by
  apply Prod.ext <;> norm_num [midpoint_eq_smul_add, smul_eq_mul] <;> ring

private theorem rectangle_vertical_segment {p q a b u v x : ℝ × ℝ}
    (hp : p.1 < q.1 ∧ p.2 < q.2) (ha : a.1 < b.1 ∧ a.2 < b.2)
    (hu : u ∈ Set.Icc p.1 q.1 ×ˢ Set.Icc p.2 q.2)
    (hv : v ∈ Set.Icc p.1 q.1 ×ˢ Set.Icc p.2 q.2)
    (hne : u ≠ v) (haxis : u.1 = v.1)
    (hxS : x ∈ openSegment ℝ u v)
    (hx : x ∈ Set.Icc a.1 b.1 ×ˢ Set.Icc a.2 b.2)
    (hdisj : Disjoint (Set.Ioo p.1 q.1 ×ˢ Set.Ioo p.2 q.2)
      (Set.Ioo a.1 b.1 ×ˢ Set.Ioo a.2 b.2))
    (hcorners : ∀ ε : Fin 2 × Fin 2, rectangleCorner a b ε ∈ segment ℝ u v →
      rectangleCorner a b ε = u ∨ rectangleCorner a b ε = v) :
    segment ℝ u v ⊆ Set.Icc a.1 b.1 ×ˢ Set.Icc a.2 b.2 := by
  have hneq : u.2 ≠ v.2 := fun h ↦ hne (Prod.ext haxis h)
  have hS : segment ℝ u v = {u.1} ×ˢ Set.Icc (min u.2 v.2) (max u.2 v.2) := by
    change segment ℝ (u.1, u.2) (v.1, v.2) = _
    rw [← haxis, ← Prod.image_mk_segment_right, segment_eq_Icc', ← Set.singleton_prod]
  have hxcoord := Prod.openSegment_subset (𝕜 := ℝ) u v hxS
  have hη : x.2 ∈ Set.Ioo (min u.2 v.2) (max u.2 v.2) := by
    simpa only [openSegment_eq_Ioo' hneq] using hxcoord.2
  have hξ : x.1 = u.1 := by
    simpa only [← haxis, openSegment_same, Set.mem_singleton_iff] using hxcoord.1
  have hx' : (u.1, x.2) ∈ Set.Icc a.1 b.1 ×ˢ Set.Icc a.2 b.2 := by
    exact ⟨by simpa only [hξ] using hx.1, hx.2⟩
  rw [hS]
  apply rectangle_vertical_containment hp ha hu.1 (le_min hu.2.1 hv.2.1)
    (max_le hu.2.2 hv.2.2) hη hx' hdisj
  intro ε hε
  have hmem : rectangleCorner a b ε ∈ segment ℝ u v := by
    rw [hS]
    exact ⟨hε.1, Set.Ioo_subset_Icc_self hε.2⟩
  rcases hcorners ε hmem with he | he
  · rw [he] at hε
    rcases le_total u.2 v.2 with h | h
    · simp [min_eq_left h, max_eq_right h] at hε
    · simp [min_eq_right h, max_eq_left h] at hε
  · rw [he] at hε
    rcases le_total u.2 v.2 with h | h
    · simp [min_eq_left h, max_eq_right h] at hε
    · simp [min_eq_right h, max_eq_left h] at hε

private theorem swap_mem_segment {u v x : ℝ × ℝ} (hx : x ∈ segment ℝ u v) :
    x.swap ∈ segment ℝ u.swap v.swap := by
  exact (image_segment ℝ (AffineEquiv.prodComm ℝ ℝ ℝ).toAffineMap u v) ▸
    Set.mem_image_of_mem _ hx

private theorem rectangle_axis_segment {p q a b u v x : ℝ × ℝ}
    (hp : p.1 < q.1 ∧ p.2 < q.2) (ha : a.1 < b.1 ∧ a.2 < b.2)
    (hu : u ∈ Set.Icc p.1 q.1 ×ˢ Set.Icc p.2 q.2)
    (hv : v ∈ Set.Icc p.1 q.1 ×ˢ Set.Icc p.2 q.2)
    (hne : u ≠ v) (haxis : u.1 = v.1 ∨ u.2 = v.2)
    (hxS : x ∈ openSegment ℝ u v)
    (hx : x ∈ Set.Icc a.1 b.1 ×ˢ Set.Icc a.2 b.2)
    (hdisj : Disjoint (Set.Ioo p.1 q.1 ×ˢ Set.Ioo p.2 q.2)
      (Set.Ioo a.1 b.1 ×ˢ Set.Ioo a.2 b.2))
    (hcorners : ∀ ε : Fin 2 × Fin 2, rectangleCorner a b ε ∈ segment ℝ u v →
      rectangleCorner a b ε = u ∨ rectangleCorner a b ε = v) :
    segment ℝ u v ⊆ Set.Icc a.1 b.1 ×ˢ Set.Icc a.2 b.2 := by
  rcases haxis with haxis | haxis
  · exact rectangle_vertical_segment hp ha hu hv hne haxis hxS hx hdisj hcorners
  · have hd : Disjoint (Set.Ioo p.2 q.2 ×ˢ Set.Ioo p.1 q.1)
        (Set.Ioo a.2 b.2 ×ˢ Set.Ioo a.1 b.1) := by
      refine Set.disjoint_left.mpr ?_
      intro x hxp hxa
      exact Set.disjoint_left.mp hdisj
        (show x.swap ∈ _ from ⟨hxp.2, hxp.1⟩)
        (show x.swap ∈ _ from ⟨hxa.2, hxa.1⟩)
    have hxS' : x.swap ∈ openSegment ℝ u.swap v.swap :=
      (image_openSegment ℝ (AffineEquiv.prodComm ℝ ℝ ℝ).toAffineMap u v) ▸
        Set.mem_image_of_mem _ hxS
    have hc : ∀ ε : Fin 2 × Fin 2,
        rectangleCorner a.swap b.swap ε ∈ segment ℝ u.swap v.swap →
        rectangleCorner a.swap b.swap ε = u.swap ∨
          rectangleCorner a.swap b.swap ε = v.swap := by
      intro ε hε
      have hs : rectangleCorner a b (ε.2, ε.1) ∈ segment ℝ u v := by
        simpa [rectangleCorner] using swap_mem_segment hε
      rcases hcorners (ε.2, ε.1) hs with h | h
      · exact Or.inl (by simpa [rectangleCorner] using congrArg Prod.swap h)
      · exact Or.inr (by simpa [rectangleCorner] using congrArg Prod.swap h)
    have hsub := rectangle_vertical_segment (p := p.swap) (q := q.swap)
      (a := a.swap) (b := b.swap) (u := u.swap) (v := v.swap)
      ⟨hp.2, hp.1⟩ ⟨ha.2, ha.1⟩ ⟨hu.2, hu.1⟩ ⟨hv.2, hv.1⟩
      (fun h ↦ hne (Prod.swap_injective h)) haxis hxS' ⟨hx.2, hx.1⟩ hd hc
    intro x hxS
    have hr := hsub (swap_mem_segment hxS)
    exact ⟨hr.2, hr.1⟩

/-- The lower-left corner of a dyadic cell lies strictly below and to the left
of its upper-right corner. Source: area-law Section 11, lines 299–310. -/
theorem dyadicCellCorner_lt (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ) :
    (dyadicCellCorner o ℓ z (0, 0)).1 < (dyadicCellCorner o ℓ z (1, 1)).1 ∧
      (dyadicCellCorner o ℓ z (0, 0)).2 < (dyadicCellCorner o ℓ z (1, 1)).2 := by
  have ht : 0 < (2 : ℝ) ^ ℓ := by positivity
  constructor <;> norm_num [dyadicCellCorner]

/-- The interior of a dyadic cell is the open rectangle spanned by its extreme
corners. Source: area-law Section 11, lines 299–310. -/
theorem interior_dyadicCell_eq_corners (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ) :
    interior (dyadicCell o ℓ z) =
      Set.Ioo (dyadicCellCorner o ℓ z (0, 0)).1 (dyadicCellCorner o ℓ z (1, 1)).1 ×ˢ
        Set.Ioo (dyadicCellCorner o ℓ z (0, 0)).2 (dyadicCellCorner o ℓ z (1, 1)).2 := by
  simp [dyadicCell, interior_prod_eq, interior_Ico, dyadicCellCorner]

/-- The closure of a dyadic cell is the closed rectangle spanned by its extreme
corners. Source: area-law Section 11, lines 299–310. -/
theorem closure_dyadicCell_eq_corners (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ) :
    closure (dyadicCell o ℓ z) =
      Set.Icc (dyadicCellCorner o ℓ z (0, 0)).1 (dyadicCellCorner o ℓ z (1, 1)).1 ×ˢ
        Set.Icc (dyadicCellCorner o ℓ z (0, 0)).2 (dyadicCellCorner o ℓ z (1, 1)).2 := by
  simp [closure_dyadicCell, dyadicCellCorner]

/-- The rectangle corners spanned by the extreme corners of a dyadic cell are
its four corners. Source: area-law Section 11, lines 299–310. -/
theorem rectangleCorner_eq_dyadicCellCorner (o : ℝ × ℝ) (ℓ : ℕ)
    (z : ℤ × ℤ) (ε : Fin 2 × Fin 2) :
    rectangleCorner (dyadicCellCorner o ℓ z (0, 0)) (dyadicCellCorner o ℓ z (1, 1)) ε =
      dyadicCellCorner o ℓ z ε := by
  rcases ε with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> norm_num [rectangleCorner, dyadicCellCorner]

private theorem unsplit_geometry (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ) (s : Fin 4) :
    let a := cellFanStart o ℓ z (fun _ ↦ false) ⟨s, 0⟩
    let b := cellFanEnd o ℓ z (fun _ ↦ false) ⟨s, 0⟩
    let p := dyadicCellCorner o ℓ z (0, 0)
    let q := dyadicCellCorner o ℓ z (1, 1)
    a ≠ b ∧ ((a.1 = b.1 ∧ (a.1 = p.1 ∨ a.1 = q.1)) ∨
      (a.2 = b.2 ∧ (a.2 = p.2 ∨ a.2 = q.2))) := by
  dsimp only
  have h := cellFan_unsplit_endpoints_coordinates o ℓ z s
  have ha := congrArg Prod.fst h
  have hb := congrArg Prod.snd h
  have ht : 0 < (2 : ℝ) ^ ℓ := by positivity
  constructor
  · intro he
    fin_cases s <;> norm_num at ha hb <;> rw [ha, hb] at he
    all_goals
      have he₁ := congrArg Prod.fst he
      have he₂ := congrArg Prod.snd he
      dsimp only at he₁ he₂
      nlinarith
  · fin_cases s <;> norm_num at ha hb <;> rw [ha, hb]
    · exact Or.inl ⟨rfl, Or.inr (by simp [dyadicCellCorner])⟩
    · exact Or.inr ⟨rfl, Or.inr (by simp [dyadicCellCorner])⟩
    · exact Or.inl ⟨rfl, Or.inl (by simp [dyadicCellCorner])⟩
    · exact Or.inr ⟨rfl, Or.inl (by simp [dyadicCellCorner])⟩

/-- Every optional elementary side is nondegenerate and axis-parallel, with
its constant coordinate equal to a boundary coordinate of its dyadic square.
Source: area-law Section 11, lines 299–310. -/
theorem cellFan_elementary_geometry (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (i : CellFanSlot split) :
    let a := cellFanStart o ℓ z split i
    let b := cellFanEnd o ℓ z split i
    let p := dyadicCellCorner o ℓ z (0, 0)
    let q := dyadicCellCorner o ℓ z (1, 1)
    a ≠ b ∧ ((a.1 = b.1 ∧ (a.1 = p.1 ∨ a.1 = q.1)) ∨
      (a.2 = b.2 ∧ (a.2 = p.2 ∨ a.2 = q.2))) := by
  dsimp only
  obtain ⟨hne, haxis⟩ := unsplit_geometry o ℓ z i.1
  rcases cellFan_elementary_endpoints_cases o ℓ z split i with ⟨_, ha, hb⟩ |
    ⟨_, ha, hb⟩ | ⟨_, ha, hb⟩ <;> rw [ha, hb]
  · exact ⟨hne, haxis⟩
  · refine ⟨fun h ↦ hne ((midpoint_eq_left_iff ℝ).mp h.symm), ?_⟩
    rcases haxis with ⟨he, hbound⟩ | ⟨he, hbound⟩
    · exact Or.inl ⟨by rw [midpoint_prod_eq]; dsimp only; linarith, hbound⟩
    · exact Or.inr ⟨by rw [midpoint_prod_eq]; dsimp only; linarith, hbound⟩
  · refine ⟨fun h ↦ hne ((midpoint_eq_right_iff ℝ).mp h), ?_⟩
    rcases haxis with ⟨he, hbound⟩ | ⟨he, hbound⟩
    · have hm : (midpoint ℝ
          (cellFanStart o ℓ z (fun _ ↦ false) ⟨i.1, 0⟩)
          (cellFanEnd o ℓ z (fun _ ↦ false) ⟨i.1, 0⟩)).1 =
          (cellFanStart o ℓ z (fun _ ↦ false) ⟨i.1, 0⟩).1 := by
        rw [midpoint_prod_eq]; dsimp only; linarith
      exact Or.inl ⟨by rw [hm]; exact he, by rwa [hm]⟩
    · have hm : (midpoint ℝ
          (cellFanStart o ℓ z (fun _ ↦ false) ⟨i.1, 0⟩)
          (cellFanEnd o ℓ z (fun _ ↦ false) ⟨i.1, 0⟩)).2 =
          (cellFanStart o ℓ z (fun _ ↦ false) ⟨i.1, 0⟩).2 := by
        rw [midpoint_prod_eq]; dsimp only; linarith
      exact Or.inr ⟨by rw [hm]; exact he, by rwa [hm]⟩

private theorem elementary_endpoints_closed (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (i : CellFanSlot split) :
    cellFanStart o ℓ z split i ∈ closure (dyadicCell o ℓ z) ∧
      cellFanEnd o ℓ z split i ∈ closure (dyadicCell o ℓ z) := by
  have h := (cellFan_vertices_mem_beltCellMarks o ℓ z split).2 i
  exact ⟨beltCellMarks_subset_closure_dyadicCell o ℓ z h.1,
    beltCellMarks_subset_closure_dyadicCell o ℓ z h.2⟩

private theorem cell_contains_elementary_segment (o : ℝ × ℝ) (ℓ j : ℕ)
    (z w : ℤ × ℤ) (split : Fin 4 → Bool) (i : CellFanSlot split)
    (x : ℝ × ℝ)
    (hd : Disjoint (dyadicCell o ℓ z) (dyadicCell o j w))
    (hxS : x ∈ openSegment ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i))
    (hx : x ∈ closure (dyadicCell o j w))
    (hcorners : ∀ ε : Fin 2 × Fin 2, dyadicCellCorner o j w ε ∈ segment ℝ
        (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i) →
      dyadicCellCorner o j w ε = cellFanStart o ℓ z split i ∨
        dyadicCellCorner o j w ε = cellFanEnd o ℓ z split i) :
    segment ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i) ⊆
      closure (dyadicCell o j w) := by
  obtain ⟨ha, hb⟩ := elementary_endpoints_closed o ℓ z split i
  obtain ⟨hne, haxis⟩ := cellFan_elementary_geometry o ℓ z split i
  have hdi := hd.mono interior_subset interior_subset
  rw [interior_dyadicCell_eq_corners, interior_dyadicCell_eq_corners] at hdi
  rw [closure_dyadicCell_eq_corners] at ha hb hx ⊢
  apply rectangle_axis_segment (dyadicCellCorner_lt o ℓ z) (dyadicCellCorner_lt o j w)
    ha hb hne (haxis.imp And.left And.left) hxS hx hdi
  intro ε hε
  rw [rectangleCorner_eq_dyadicCellCorner] at hε ⊢
  exact hcorners ε hε

private theorem elementary_midpoint_not_mem_interior (o : ℝ × ℝ) (ℓ : ℕ)
    (z : ℤ × ℤ) (split : Fin 4 → Bool) (i : CellFanSlot split) :
    midpoint ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i) ∉
      interior (closure (dyadicCell o ℓ z)) := by
  rw [closure_dyadicCell_eq_corners, interior_prod_eq, interior_Icc, interior_Icc]
  intro hx
  rw [midpoint_prod_eq] at hx
  rcases (cellFan_elementary_geometry o ℓ z split i).2 with ⟨he, hbound⟩ | ⟨he, hbound⟩
  · have hm : ((cellFanStart o ℓ z split i).1 + (cellFanEnd o ℓ z split i).1) / 2 =
        (cellFanStart o ℓ z split i).1 := by linarith
    rw [hm] at hx
    rcases hbound with h | h <;> simp [h] at hx
  · have hm : ((cellFanStart o ℓ z split i).2 + (cellFanEnd o ℓ z split i).2) / 2 =
        (cellFanStart o ℓ z split i).2 := by linarith
    rw [hm] at hx
    rcases hbound with h | h <;> simp [h] at hx

/-- An open elementary-side contact with the actual dummy closure extends to
the whole segment. Arbitrary optional midpoint subdivisions are permitted.
Source: area-law Section 11, `prop:two-families`, lines 154–177 and 299–310. -/
theorem fineLayer_elementarySide_subset_dummy_of_mem_openSegment
    (o : ℝ × ℝ) (k₀ k : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (z : ℤ × ℤ) (split : Fin 4 → Bool) (i : CellFanSlot split)
    (x : ℝ × ℝ) (hC : 2 ≤ C) (hk₀ : k₀ ≤ k)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (hx : x ∈ openSegment ℝ
      (cellFanStart o (fineScaleIndex k) z split i)
      (cellFanEnd o (fineScaleIndex k) z split i))
    (hxN : x ∈ closure (dyadicNeighborhood o k₀ Z C)) :
    segment ℝ (cellFanStart o (fineScaleIndex k) z split i)
      (cellFanEnd o (fineScaleIndex k) z split i) ⊆
        closure (dyadicNeighborhood o k₀ Z C) := by
  rw [dyadicNeighborhood, Finset.closure_biUnion] at hxN
  obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hxN
  have hsub : dyadicCell o k₀ w ⊆ dyadicNeighborhood o k₀ Z C :=
    fun y hy ↦ Set.mem_iUnion₂.mpr ⟨w, hw, hy⟩
  have href := dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices o k
    (fineScaleIndex k) Z C z (fineScaleIndex_le k) hz
  have hd := (dyadicNeighborhood_disjoint_later_layer o Z C k₀ k hk₀).symm.mono
    href hsub
  have hseg := cell_contains_elementary_segment o (fineScaleIndex k) k₀ z w
    split i x hd hx hxw (fun ε hε ↦ dyadicNeighborhood_corner_on_elementarySide
      o k₀ k Z C z w split i ε hC hk₀ hz hw hε)
  exact hseg.trans (closure_mono hsub)

/-- Every actual elementary side has an opposing closed region containing its
whole segment: either the initial dummy neighborhood or an actual distinct fine
cell at or above the lower layer index. The actual plane cover supplies the
opposing region in an outward neighborhood; corner exclusion extends its
contact across the whole elementary segment.
Source: area-law Section 11, `prop:two-families`, lines 154–181, and the belt
subdivision and opposing-region assertion, lines 299–310. -/
theorem exists_elementarySide_opponent (o : ℝ × ℝ) (k₀ k : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (z : ℤ × ℤ)
    (i : CellFanSlot (fineLayerSplitMask o k₀ k Z C z))
    (hC : 2 ≤ C) (hk : 50000000 ≤ k) (hk₀ : k₀ ≤ k)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C) :
    segment ℝ
        (cellFanStart o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i)
        (cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i) ⊆
        closure (dyadicNeighborhood o k₀ Z C) ∨
      ∃ h ≥ k₀, ∃ w ∈ fineLayerIndices o h (fineScaleIndex h) Z C,
        (k, z) ≠ (h, w) ∧ segment ℝ
          (cellFanStart o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i)
          (cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i) ⊆
          closure (dyadicCell o (fineScaleIndex h) w) := by
  classical
  let split := fineLayerSplitMask o k₀ k Z C z
  let x := midpoint ℝ (cellFanStart o (fineScaleIndex k) z split i)
    (cellFanEnd o (fineScaleIndex k) z split i)
  let H := (Finset.Icc (k - 1) (k + 1)).filter (fun h ↦ k₀ ≤ h)
  let F := H.biUnion (fun h ↦
    (fineLayerIndices o h (fineScaleIndex h) Z C).image (fun w ↦ (h, w)))
  let G := F.erase (k, z)
  let U := Metric.ball x (10 * (2 : ℝ) ^ fineScaleIndex k) ∩
    (closure (dyadicCell o (fineScaleIndex k) z))ᶜ
  have href := dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices o k
    (fineScaleIndex k) Z C z (fineScaleIndex_le k) hz
  obtain ⟨ha, hb⟩ := elementary_endpoints_closed o (fineScaleIndex k) z split i
  have hxref : x ∈ closure (dyadicCell o (fineScaleIndex k) z) :=
    (convex_closure_dyadicCell o (fineScaleIndex k) z).midpoint_mem ha hb
  have hxD := closure_mono href hxref
  obtain ⟨v, hv, _⟩ := dyadicLayer_exists_dist_le o k Z C x hxD
  have hZ : Z.Nonempty := ⟨v, hv⟩
  have hxU : x ∈ closure U := by
    apply Metric.isOpen_ball.inter_closure
    refine ⟨Metric.mem_ball_self (by positivity), ?_⟩
    rw [closure_compl]
    exact elementary_midpoint_not_mem_interior o (fineScaleIndex k) z split i
  have hU : U ⊆ dyadicNeighborhood o k₀ Z C ∪
      ⋃ p ∈ G, dyadicCell o (fineScaleIndex p.1) p.2 := by
    intro y hy
    by_cases hyN : y ∈ dyadicNeighborhood o k₀ Z C
    · exact Set.mem_union_left _ hyN
    · obtain ⟨⟨h, w⟩, ⟨hh₀, hw, hyw⟩, _⟩ :=
        exists_unique_fineCell_of_not_mem_dyadicNeighborhood o Z C k₀ hZ hC y hyN
      have hyD := subset_closure
        (dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices o h
          (fineScaleIndex h) Z C w (fineScaleIndex_le h) hw hyw)
      have hnear := dyadicLayer_nearby_indices o k h Z C x y hC hk hxD hyD
        (by simpa only [Metric.mem_ball, dist_comm] using hy.1)
      have hne : (h, w) ≠ (k, z) := by
        intro he
        rcases Prod.mk.inj he with ⟨rfl, rfl⟩
        exact hy.2 (subset_closure hyw)
      have hh : h ∈ H := Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, hnear.1⟩, hh₀⟩
      have hp : (h, w) ∈ G := Finset.mem_erase.mpr ⟨hne,
        Finset.mem_biUnion.mpr ⟨h, hh, Finset.mem_image.mpr ⟨w, hw, rfl⟩⟩⟩
      exact Set.mem_union_right _ (Set.mem_iUnion₂.mpr ⟨(h, w), hp, hyw⟩)
  have hxcover := closure_mono hU hxU
  rw [closure_union, Finset.closure_biUnion] at hxcover
  rcases hxcover with hxN | hxF
  · exact Or.inl (fineLayer_elementarySide_subset_dummy_of_mem_openSegment o k₀ k Z C z
      split i x hC hk₀ hz (midpoint_mem_openSegment (𝕜 := ℝ) _ _) hxN)
  · obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hxF
    obtain ⟨hne, hpF⟩ := Finset.mem_erase.mp hp
    obtain ⟨h, hh, hpw⟩ := Finset.mem_biUnion.mp hpF
    obtain ⟨w, hw, he⟩ := Finset.mem_image.mp hpw
    subst p
    have hh₀ := (Finset.mem_filter.mp hh).2
    have hd := fineLayer_cells_disjoint o k h Z C z w hz hw hne.symm
    refine Or.inr ⟨h, hh₀, w, hw, hne.symm, ?_⟩
    exact cell_contains_elementary_segment o (fineScaleIndex k) (fineScaleIndex h)
      z w split i x hd (midpoint_mem_openSegment (𝕜 := ℝ) _ _) hxp
      (fun ε hε ↦ fineLayer_corner_on_elementarySide
        o k₀ k h Z C z w i ε hC hk hz hh₀ hw hε)

end ElementarySideOpponents

section ElementarySideOpponentUniqueness

/-!
## Uniqueness of the region opposing an elementary side

For dilation width at least two, take an actual reference fine cell in a layer
of index at least 50,000,000 and no smaller than the initial layer index.
Every elementary side of its actual midpoint subdivision faces exactly one
opposing region: the initial dummy neighborhood, or an actual distinct fine
cell. The uniqueness follows from disjoint interiors. Two opposing rectangles
on the same side of the reference rectangle would overlap near an interior
point of the elementary side. Actual corner exclusion prevents the dummy
boundary from changing at that point.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, lines 299–316.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

private theorem interval_disjoint_cases {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hdisj : Disjoint (Set.Ioo a b) (Set.Ioo c d)) : b ≤ c ∨ d ≤ a := by
  rw [Set.Ioo_disjoint_Ioo, min_le_iff, le_max_iff, le_max_iff] at hdisj
  rcases hdisj with (h | h) | h | h
  all_goals first | exact Or.inl h | exact Or.inr h | linarith

private theorem interval_three_disjoint {a b c d e f x : ℝ}
    (hab : a < b) (hcd : c < d) (hef : e < f)
    (hx₁ : x ∈ Set.Icc a b) (hx₂ : x ∈ Set.Icc c d) (hx₃ : x ∈ Set.Icc e f)
    (h₁₂ : Disjoint (Set.Ioo a b) (Set.Ioo c d))
    (h₁₃ : Disjoint (Set.Ioo a b) (Set.Ioo e f))
    (h₂₃ : Disjoint (Set.Ioo c d) (Set.Ioo e f)) : False := by
  rcases interval_disjoint_cases hab hcd h₁₂ with h | h <;>
    rcases interval_disjoint_cases hab hef h₁₃ with h' | h' <;>
    rcases interval_disjoint_cases hcd hef h₂₃ with h'' | h'' <;> linarith [hx₁.1, hx₁.2,
      hx₂.1, hx₂.2, hx₃.1, hx₃.2]

private theorem rectangle_tangential_strict {p q a b : ℝ × ℝ} {ξ η : ℝ}
    (hp : p.1 < q.1 ∧ p.2 < q.2) (ha : a.1 < b.1 ∧ a.2 < b.2)
    (hξp : ξ ∈ Set.Icc p.1 q.1) (hηp : η ∈ Set.Ioo p.2 q.2)
    (hx : (ξ, η) ∈ Set.Icc a.1 b.1 ×ˢ Set.Icc a.2 b.2)
    (hdisj : Disjoint (Set.Ioo p.1 q.1 ×ˢ Set.Ioo p.2 q.2)
      (Set.Ioo a.1 b.1 ×ˢ Set.Ioo a.2 b.2))
    (hcorners : ∀ ε : Fin 2 × Fin 2, rectangleCorner a b ε ≠ (ξ, η)) :
    η ∈ Set.Ioo a.2 b.2 := by
  rcases Set.disjoint_prod.mp hdisj with hn | ht
  · have hboundary : ξ = a.1 ∨ ξ = b.1 := by
      rcases interval_disjoint_cases hp.1 ha.1 hn with h | h
      · left
        linarith [hξp.2, hx.1.1]
      · right
        linarith [hξp.1, hx.1.2]
    by_contra hy
    have hη : η = a.2 ∨ η = b.2 := by
      simp only [Set.mem_Ioo, not_and_or, not_lt] at hy
      rcases hy with hy | hy
      · exact Or.inl (le_antisymm hy hx.2.1)
      · exact Or.inr (le_antisymm hx.2.2 hy)
    rcases hboundary with hξ | hξ <;> rcases hη with hη | hη
    · exact hcorners (0, 0) (by simp [rectangleCorner, hξ, hη])
    · exact hcorners (0, 1) (by simp [rectangleCorner, hξ, hη])
    · exact hcorners (1, 0) (by simp [rectangleCorner, hξ, hη])
    · exact hcorners (1, 1) (by simp [rectangleCorner, hξ, hη])
  · rcases interval_disjoint_cases hp.2 ha.2 ht with h | h <;>
      exfalso <;> linarith [hηp.1, hηp.2, hx.2.1, hx.2.2]

private theorem rectangle_three_vertical {p q a b c d : ℝ × ℝ} {ξ η : ℝ}
    (hp : p.1 < q.1 ∧ p.2 < q.2) (ha : a.1 < b.1 ∧ a.2 < b.2)
    (hc : c.1 < d.1 ∧ c.2 < d.2)
    (hξp : ξ ∈ Set.Icc p.1 q.1) (hηp : η ∈ Set.Ioo p.2 q.2)
    (hξa : ξ ∈ Set.Icc a.1 b.1) (hηa : η ∈ Set.Ioo a.2 b.2)
    (hξc : ξ ∈ Set.Icc c.1 d.1) (hηc : η ∈ Set.Ioo c.2 d.2)
    (hpa : Disjoint (Set.Ioo p.1 q.1 ×ˢ Set.Ioo p.2 q.2)
      (Set.Ioo a.1 b.1 ×ˢ Set.Ioo a.2 b.2))
    (hpc : Disjoint (Set.Ioo p.1 q.1 ×ˢ Set.Ioo p.2 q.2)
      (Set.Ioo c.1 d.1 ×ˢ Set.Ioo c.2 d.2))
    (hac : Disjoint (Set.Ioo a.1 b.1 ×ˢ Set.Ioo a.2 b.2)
      (Set.Ioo c.1 d.1 ×ˢ Set.Ioo c.2 d.2)) : False := by
  have normal_disjoint {l r s t : ℝ × ℝ}
      (hηl : η ∈ Set.Ioo l.2 r.2) (hηs : η ∈ Set.Ioo s.2 t.2)
      (hd : Disjoint (Set.Ioo l.1 r.1 ×ˢ Set.Ioo l.2 r.2)
        (Set.Ioo s.1 t.1 ×ˢ Set.Ioo s.2 t.2)) :
      Disjoint (Set.Ioo l.1 r.1) (Set.Ioo s.1 t.1) := by
    rcases Set.disjoint_prod.mp hd with hd | hd
    · exact hd
    · exact False.elim (Set.disjoint_left.mp hd hηl hηs)
  exact interval_three_disjoint hp.1 ha.1 hc.1 hξp hξa hξc
    (normal_disjoint hηp hηa hpa) (normal_disjoint hηp hηc hpc)
    (normal_disjoint hηa hηc hac)

private theorem rectangle_vertical_no_three {p q a b c d u v : ℝ × ℝ}
    (hp : p.1 < q.1 ∧ p.2 < q.2) (ha : a.1 < b.1 ∧ a.2 < b.2)
    (hc : c.1 < d.1 ∧ c.2 < d.2)
    (hup : u ∈ Set.Icc p.1 q.1 ×ˢ Set.Icc p.2 q.2)
    (hvp : v ∈ Set.Icc p.1 q.1 ×ˢ Set.Icc p.2 q.2)
    (hua : u ∈ Set.Icc a.1 b.1 ×ˢ Set.Icc a.2 b.2)
    (hva : v ∈ Set.Icc a.1 b.1 ×ˢ Set.Icc a.2 b.2)
    (hx : midpoint ℝ u v ∈ Set.Icc c.1 d.1 ×ˢ Set.Icc c.2 d.2)
    (hne : u ≠ v) (haxis : u.1 = v.1)
    (hcorners : ∀ ε : Fin 2 × Fin 2, rectangleCorner c d ε ≠ midpoint ℝ u v)
    (hpa : Disjoint (Set.Ioo p.1 q.1 ×ˢ Set.Ioo p.2 q.2)
      (Set.Ioo a.1 b.1 ×ˢ Set.Ioo a.2 b.2))
    (hpc : Disjoint (Set.Ioo p.1 q.1 ×ˢ Set.Ioo p.2 q.2)
      (Set.Ioo c.1 d.1 ×ˢ Set.Ioo c.2 d.2))
    (hac : Disjoint (Set.Ioo a.1 b.1 ×ˢ Set.Ioo a.2 b.2)
      (Set.Ioo c.1 d.1 ×ˢ Set.Ioo c.2 d.2)) : False := by
  have hneq : u.2 ≠ v.2 := fun h ↦ hne (Prod.ext haxis h)
  have strict_midpoint {l r : ℝ} (hu : u.2 ∈ Set.Icc l r)
      (hv : v.2 ∈ Set.Icc l r) : (u.2 + v.2) / 2 ∈ Set.Ioo l r := by
    rcases lt_or_gt_of_ne hneq with h | h <;> constructor <;>
      linarith [hu.1, hu.2, hv.1, hv.2]
  have hm : (u.1 + v.1) / 2 = u.1 := by linarith
  rw [midpoint_prod_eq, hm] at hx hcorners
  have hηc := rectangle_tangential_strict hp hc hup.1
    (strict_midpoint hup.2 hvp.2) hx hpc hcorners
  exact rectangle_three_vertical hp ha hc hup.1 (strict_midpoint hup.2 hvp.2)
    hua.1 (strict_midpoint hua.2 hva.2) hx.1 hηc hpa hpc hac

private theorem rectangle_axis_no_three {p q a b c d u v : ℝ × ℝ}
    (hp : p.1 < q.1 ∧ p.2 < q.2) (ha : a.1 < b.1 ∧ a.2 < b.2)
    (hc : c.1 < d.1 ∧ c.2 < d.2)
    (hup : u ∈ Set.Icc p.1 q.1 ×ˢ Set.Icc p.2 q.2)
    (hvp : v ∈ Set.Icc p.1 q.1 ×ˢ Set.Icc p.2 q.2)
    (hua : u ∈ Set.Icc a.1 b.1 ×ˢ Set.Icc a.2 b.2)
    (hva : v ∈ Set.Icc a.1 b.1 ×ˢ Set.Icc a.2 b.2)
    (hx : midpoint ℝ u v ∈ Set.Icc c.1 d.1 ×ˢ Set.Icc c.2 d.2)
    (hne : u ≠ v) (haxis : u.1 = v.1 ∨ u.2 = v.2)
    (hcorners : ∀ ε : Fin 2 × Fin 2, rectangleCorner c d ε ≠ midpoint ℝ u v)
    (hpa : Disjoint (Set.Ioo p.1 q.1 ×ˢ Set.Ioo p.2 q.2)
      (Set.Ioo a.1 b.1 ×ˢ Set.Ioo a.2 b.2))
    (hpc : Disjoint (Set.Ioo p.1 q.1 ×ˢ Set.Ioo p.2 q.2)
      (Set.Ioo c.1 d.1 ×ˢ Set.Ioo c.2 d.2))
    (hac : Disjoint (Set.Ioo a.1 b.1 ×ˢ Set.Ioo a.2 b.2)
      (Set.Ioo c.1 d.1 ×ˢ Set.Ioo c.2 d.2)) : False := by
  rcases haxis with haxis | haxis
  · exact rectangle_vertical_no_three hp ha hc hup hvp hua hva hx hne haxis
      hcorners hpa hpc hac
  · have hm : (midpoint ℝ u v).swap = midpoint ℝ u.swap v.swap :=
      (AffineEquiv.prodComm ℝ ℝ ℝ).map_midpoint u v
    have hcorners' : ∀ ε : Fin 2 × Fin 2,
        rectangleCorner c.swap d.swap ε ≠ midpoint ℝ u.swap v.swap := by
      intro ε he
      apply hcorners (ε.2, ε.1)
      simpa [rectangleCorner, ← hm] using congrArg Prod.swap he
    have swapped_disjoint {l r s t : ℝ × ℝ}
        (hd : Disjoint (Set.Ioo l.1 r.1 ×ˢ Set.Ioo l.2 r.2)
          (Set.Ioo s.1 t.1 ×ˢ Set.Ioo s.2 t.2)) :
        Disjoint (Set.Ioo l.2 r.2 ×ˢ Set.Ioo l.1 r.1)
          (Set.Ioo s.2 t.2 ×ˢ Set.Ioo s.1 t.1) :=
      Set.disjoint_prod.mpr (Set.disjoint_prod.mp hd).symm
    have hx' : midpoint ℝ u.swap v.swap ∈
        Set.Icc c.2 d.2 ×ˢ Set.Icc c.1 d.1 := by
      rw [← hm]
      exact ⟨hx.2, hx.1⟩
    exact rectangle_vertical_no_three (p := p.swap) (q := q.swap)
      (a := a.swap) (b := b.swap) (c := c.swap) (d := d.swap)
      (u := u.swap) (v := v.swap)
      ⟨hp.2, hp.1⟩ ⟨ha.2, ha.1⟩ ⟨hc.2, hc.1⟩
      ⟨hup.2, hup.1⟩ ⟨hvp.2, hvp.1⟩ ⟨hua.2, hua.1⟩ ⟨hva.2, hva.1⟩ hx'
      (fun h ↦ hne (Prod.swap_injective h)) haxis hcorners'
      (swapped_disjoint hpa) (swapped_disjoint hpc) (swapped_disjoint hac)

private theorem cells_on_elementarySide_absurd (o : ℝ × ℝ) (ℓ j n : ℕ)
    (z w t : ℤ × ℤ) (split : Fin 4 → Bool) (i : CellFanSlot split)
    (hzw : Disjoint (dyadicCell o ℓ z) (dyadicCell o j w))
    (hzt : Disjoint (dyadicCell o ℓ z) (dyadicCell o n t))
    (hwt : Disjoint (dyadicCell o j w) (dyadicCell o n t))
    (hside : segment ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i) ⊆
      closure (dyadicCell o j w))
    (hx : midpoint ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i) ∈
      closure (dyadicCell o n t))
    (hcorners : ∀ ε : Fin 2 × Fin 2, dyadicCellCorner o n t ε ∈
      segment ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i) →
      dyadicCellCorner o n t ε = cellFanStart o ℓ z split i ∨
        dyadicCellCorner o n t ε = cellFanEnd o ℓ z split i) : False := by
  obtain ⟨hne, haxis⟩ := cellFan_elementary_geometry o ℓ z split i
  have hcorners' (ε : Fin 2 × Fin 2) :
      rectangleCorner (dyadicCellCorner o n t (0, 0)) (dyadicCellCorner o n t (1, 1)) ε ≠
        midpoint ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i) := by
    rw [rectangleCorner_eq_dyadicCellCorner]
    intro he
    have hm := midpoint_mem_segment (𝕜 := ℝ) (cellFanStart o ℓ z split i)
      (cellFanEnd o ℓ z split i)
    rcases hcorners ε (he ▸ hm) with h | h
    · exact hne ((midpoint_eq_left_iff ℝ).mp (he.symm.trans h))
    · exact hne ((midpoint_eq_right_iff ℝ).mp (he.symm.trans h))
  have disjoint_box (r s : ℕ) (v u : ℤ × ℤ)
      (hd : Disjoint (dyadicCell o r v) (dyadicCell o s u)) :
      Disjoint (Set.Ioo (dyadicCellCorner o r v (0, 0)).1 (dyadicCellCorner o r v (1, 1)).1 ×ˢ
        Set.Ioo (dyadicCellCorner o r v (0, 0)).2 (dyadicCellCorner o r v (1, 1)).2)
        (Set.Ioo (dyadicCellCorner o s u (0, 0)).1 (dyadicCellCorner o s u (1, 1)).1 ×ˢ
          Set.Ioo (dyadicCellCorner o s u (0, 0)).2 (dyadicCellCorner o s u (1, 1)).2) := by
    rw [← interior_dyadicCell_eq_corners, ← interior_dyadicCell_eq_corners]
    exact hd.mono interior_subset interior_subset
  obtain ⟨ha, hb⟩ := (cellFan_vertices_mem_beltCellMarks o ℓ z split).2 i
  have haR := beltCellMarks_subset_closure_dyadicCell o ℓ z ha
  have hbR := beltCellMarks_subset_closure_dyadicCell o ℓ z hb
  have haW := hside (left_mem_segment ℝ _ _)
  have hbW := hside (right_mem_segment ℝ _ _)
  rw [closure_dyadicCell_eq_corners] at haR hbR haW hbW hx
  exact rectangle_axis_no_three (dyadicCellCorner_lt o ℓ z) (dyadicCellCorner_lt o j w)
    (dyadicCellCorner_lt o n t) haR hbR haW hbW hx hne (haxis.imp And.left And.left) hcorners'
    (disjoint_box ℓ j z w hzw) (disjoint_box ℓ n z t hzt) (disjoint_box j n w t hwt)

private theorem fine_opponents_eq (o : ℝ × ℝ) (k₀ k h j : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (z w t : ℤ × ℤ)
    (i : CellFanSlot (fineLayerSplitMask o k₀ k Z C z))
    (hC : 2 ≤ C) (hk : 50000000 ≤ k) (hj₀ : k₀ ≤ j)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (hw : w ∈ fineLayerIndices o h (fineScaleIndex h) Z C)
    (ht : t ∈ fineLayerIndices o j (fineScaleIndex j) Z C)
    (hzw : (k, z) ≠ (h, w)) (hzt : (k, z) ≠ (j, t))
    (hsidew : segment ℝ
      (cellFanStart o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i)
      (cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i) ⊆
        closure (dyadicCell o (fineScaleIndex h) w))
    (hsidet : segment ℝ
      (cellFanStart o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i)
      (cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i) ⊆
        closure (dyadicCell o (fineScaleIndex j) t)) : (h, w) = (j, t) := by
  by_contra hne
  exact cells_on_elementarySide_absurd o (fineScaleIndex k) (fineScaleIndex h)
    (fineScaleIndex j) z w t (fineLayerSplitMask o k₀ k Z C z) i
    (fineLayer_cells_disjoint o k h Z C z w hz hw hzw)
    (fineLayer_cells_disjoint o k j Z C z t hz ht hzt)
    (fineLayer_cells_disjoint o h j Z C w t hw ht hne) hsidew
    (hsidet (midpoint_mem_segment (𝕜 := ℝ) _ _))
    (fun ε hε ↦ fineLayer_corner_on_elementarySide o k₀ k j Z C z t i ε
      hC hk hz hj₀ ht hε)

private theorem dummy_fine_opponents_absurd (o : ℝ × ℝ) (k₀ k h : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (z w : ℤ × ℤ)
    (i : CellFanSlot (fineLayerSplitMask o k₀ k Z C z))
    (hC : 2 ≤ C) (hk₀ : k₀ ≤ k) (hh₀ : k₀ ≤ h)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (hw : w ∈ fineLayerIndices o h (fineScaleIndex h) Z C)
    (hne : (k, z) ≠ (h, w))
    (hsideN : segment ℝ
      (cellFanStart o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i)
      (cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i) ⊆
        closure (dyadicNeighborhood o k₀ Z C))
    (hsideW : segment ℝ
      (cellFanStart o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i)
      (cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i) ⊆
        closure (dyadicCell o (fineScaleIndex h) w)) : False := by
  have hxN := hsideN (midpoint_mem_segment (𝕜 := ℝ) _ _)
  rw [dyadicNeighborhood, Finset.closure_biUnion] at hxN
  obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hxN
  have hsub : dyadicCell o k₀ t ⊆ dyadicNeighborhood o k₀ Z C :=
    fun y hy ↦ Set.mem_iUnion₂.mpr ⟨t, ht, hy⟩
  have hzsub := dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices o k
    (fineScaleIndex k) Z C z (fineScaleIndex_le k) hz
  have hwsub := dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices o h
    (fineScaleIndex h) Z C w (fineScaleIndex_le h) hw
  exact cells_on_elementarySide_absurd o (fineScaleIndex k) (fineScaleIndex h)
    k₀ z w t (fineLayerSplitMask o k₀ k Z C z) i
    (fineLayer_cells_disjoint o k h Z C z w hz hw hne)
    ((dyadicNeighborhood_disjoint_later_layer o Z C k₀ k hk₀).symm.mono hzsub hsub)
    ((dyadicNeighborhood_disjoint_later_layer o Z C k₀ h hh₀).symm.mono hwsub hsub)
    hsideW hxt (fun ε hε ↦ dyadicNeighborhood_corner_on_elementarySide o k₀ k Z C
      z t (fineLayerSplitMask o k₀ k Z C z) i ε hC hk₀ hz ht hε)

/-- The actual region opposing an elementary side is unique, where `none`
denotes the dummy neighborhood and `some (h, w)` denotes an actual fine cell.
The entire closed elementary segment belongs to the selected closed region.
The dilation width is at least two, and the reference layer index is at least
50,000,000 and no smaller than the initial layer index.
Source: area-law Section 11, `prop:two-families`, lines 299–316. -/
theorem exists_unique_elementarySide_opponent (o : ℝ × ℝ) (k₀ k : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (z : ℤ × ℤ)
    (i : CellFanSlot (fineLayerSplitMask o k₀ k Z C z))
    (hC : 2 ≤ C) (hk : 50000000 ≤ k) (hk₀ : k₀ ≤ k)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C) :
    ∃! P : Option (ℕ × (ℤ × ℤ)),
      match P with
      | none => segment ℝ
          (cellFanStart o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i)
          (cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i) ⊆
            closure (dyadicNeighborhood o k₀ Z C)
      | some (h, w) => k₀ ≤ h ∧ w ∈ fineLayerIndices o h (fineScaleIndex h) Z C ∧
          (k, z) ≠ (h, w) ∧ segment ℝ
          (cellFanStart o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i)
          (cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i) ⊆
            closure (dyadicCell o (fineScaleIndex h) w) := by
  rcases exists_elementarySide_opponent o k₀ k Z C z i hC hk hk₀ hz with hN |
    ⟨h, hh₀, w, hw, hne, hW⟩
  · refine ⟨none, hN, ?_⟩
    intro Q hQ
    cases Q with
    | none => rfl
    | some p =>
      rcases p with ⟨j, t⟩
      rcases hQ with ⟨hj₀, ht, hzt, hT⟩
      exact False.elim (dummy_fine_opponents_absurd o k₀ k j Z C z t i
        hC hk₀ hj₀ hz ht hzt hN hT)
  · refine ⟨some (h, w), ⟨hh₀, hw, hne, hW⟩, ?_⟩
    intro Q hQ
    cases Q with
    | none =>
      exact False.elim (dummy_fine_opponents_absurd o k₀ k h Z C z w i
        hC hk₀ hh₀ hz hw hne hQ hW)
    | some p =>
      rcases p with ⟨j, t⟩
      rcases hQ with ⟨hj₀, ht, hzt, hT⟩
      exact congrArg Option.some (fine_opponents_eq o k₀ k j h Z C z t w i
        hC hk hh₀ hz ht hw hzt hne hT hW)

end ElementarySideOpponentUniqueness

end TNLean.PEPS.AreaLaw.Geometry

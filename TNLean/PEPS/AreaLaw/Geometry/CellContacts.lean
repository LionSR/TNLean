/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.SideEndpoints
import Mathlib.Order.Interval.Set.Disjoint

/-!
# Contacts between actual fine cells

Distinct actual fine cells are disjoint as half-open sets. If their closures
share more than one point, their common set is a whole side of the smaller
cell. It is either a whole side or one midpoint half of the larger cell,
with the two sides facing in opposite directions.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, lines 299–306 and 352–356.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- A whole side of the actual translated dyadic cell, oriented by its fan
endpoints. Source: area-law Section 11, lines 299–306. -/
def dyadicCellSide (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ) (s : Fin 4) : Set (ℝ × ℝ) :=
  segment ℝ (cellFanStart o ℓ z (fun _ ↦ false) ⟨s, 0⟩)
    (cellFanEnd o ℓ z (fun _ ↦ false) ⟨s, 0⟩)

/-- Distinct actual indexed fine cells are disjoint as half-open sets.
Source: area-law Section 11, lines 173–181 and 299–306. -/
theorem fineLayer_cells_disjoint (o : ℝ × ℝ) (k h : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (z w : ℤ × ℤ)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (hw : w ∈ fineLayerIndices o h (fineScaleIndex h) Z C)
    (hne : (k, z) ≠ (h, w)) :
    Disjoint (dyadicCell o (fineScaleIndex k) z)
      (dyadicCell o (fineScaleIndex h) w) := by
  by_cases hkh : k = h
  · subst h
    refine Set.disjoint_left.mpr ?_
    intro x hx hy
    have hzw := (mem_dyadicCell_iff o (fineScaleIndex k) z x).mp hx
    have hwz := (mem_dyadicCell_iff o (fineScaleIndex k) w x).mp hy
    exact hne (congrArg (fun u ↦ (k, u)) (hzw.symm.trans hwz))
  · exact (dyadicLayer_pairwiseDisjoint o Z C hkh).mono
      (dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices o k (fineScaleIndex k)
        Z C z (fineScaleIndex_le k) hz)
      (dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices o h (fineScaleIndex h)
        Z C w (fineScaleIndex_le h) hw)

private theorem vertical_segment (a b c : ℝ) (hbc : b ≤ c) :
    segment ℝ (a, b) (a, c) = {a} ×ˢ Set.Icc b c := by
  rw [← Prod.image_mk_segment_right, segment_eq_Icc hbc]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨rfl, hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨x.2, hy, Prod.ext hx.symm rfl⟩

private theorem horizontal_segment (a b c : ℝ) (hbc : a ≤ b) :
    segment ℝ (a, c) (b, c) = Set.Icc a b ×ˢ {c} := by
  rw [← Prod.image_mk_segment_left, segment_eq_Icc hbc]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, rfl⟩
  · rintro ⟨hx, hy⟩
    exact ⟨x.1, hx, Prod.ext rfl hy.symm⟩

private theorem whole_side_rectangle (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ) (s : Fin 4) :
    dyadicCellSide o ℓ z s =
    match s.val with
    | 0 => {o.1 + 2 ^ ℓ * (z.1 + 1)} ×ˢ
        Set.Icc (o.2 + 2 ^ ℓ * z.2) (o.2 + 2 ^ ℓ * (z.2 + 1))
    | 1 => Set.Icc (o.1 + 2 ^ ℓ * z.1) (o.1 + 2 ^ ℓ * (z.1 + 1)) ×ˢ
        {o.2 + 2 ^ ℓ * (z.2 + 1)}
    | 2 => {o.1 + 2 ^ ℓ * z.1} ×ˢ
        Set.Icc (o.2 + 2 ^ ℓ * z.2) (o.2 + 2 ^ ℓ * (z.2 + 1))
    | _ => Set.Icc (o.1 + 2 ^ ℓ * z.1) (o.1 + 2 ^ ℓ * (z.1 + 1)) ×ˢ
        {o.2 + 2 ^ ℓ * z.2} := by
  have hs := congrArg Prod.fst (cellFan_unsplit_endpoints_coordinates o ℓ z s)
  have he := congrArg Prod.snd (cellFan_unsplit_endpoints_coordinates o ℓ z s)
  dsimp only at hs he
  rw [dyadicCellSide, hs, he]
  have hbound (a : ℝ) (i : ℤ) : a + (2 : ℝ) ^ ℓ * i ≤ a + 2 ^ ℓ * (i + 1) := by
    have ht : 0 < (2 : ℝ) ^ ℓ := by positivity
    linarith
  fin_cases s
  · exact vertical_segment _ _ _ (hbound _ _)
  · rw [segment_symm]
    exact horizontal_segment _ _ _ (hbound _ _)
  · rw [segment_symm]
    exact vertical_segment _ _ _ (hbound _ _)
  · exact horizontal_segment _ _ _ (hbound _ _)

private theorem contact_offsets (A B r : ℝ) (hr : 0 < r) (m a b : ℤ)
    (hm : 0 < m)
    (hdisj : Disjoint
      (Set.Ico (A + r * a) (A + r * (a + 1)) ×ˢ
        Set.Ico (B + r * b) (B + r * (b + 1)))
      (Set.Ico A (A + r * m) ×ˢ Set.Ico B (B + r * m)))
    (hcontact : (Set.Icc (A + r * a) (A + r * (a + 1)) ×ˢ
        Set.Icc (B + r * b) (B + r * (b + 1)) ∩
      Set.Icc A (A + r * m) ×ˢ Set.Icc B (B + r * m)).Nontrivial) :
    (a = -1 ∧ 0 ≤ b ∧ b < m) ∨ (a = m ∧ 0 ≤ b ∧ b < m) ∨
      (b = -1 ∧ 0 ≤ a ∧ a < m) ∨ (b = m ∧ 0 ≤ a ∧ a < m) := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hcontact
  simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_Icc] at hx hy
  have ha0 : (-1 : ℤ) ≤ a := by
    exact_mod_cast (show (-1 : ℝ) ≤ a by nlinarith [hx.1.1.2, hx.2.1.1])
  have ham : a ≤ m := by
    exact_mod_cast (show (a : ℝ) ≤ m by nlinarith [hx.1.1.1, hx.2.1.2])
  have hb0 : (-1 : ℤ) ≤ b := by
    exact_mod_cast (show (-1 : ℝ) ≤ b by nlinarith [hx.1.2.2, hx.2.2.1])
  have hbm : b ≤ m := by
    exact_mod_cast (show (b : ℝ) ≤ m by nlinarith [hx.1.2.1, hx.2.2.2])
  have hedge : a = -1 ∨ a = m ∨ b = -1 ∨ b = m := by
    by_contra! h
    have ha : 0 ≤ a ∧ a < m := by omega
    have hb : 0 ≤ b ∧ b < m := by omega
    have ha' : (0 : ℝ) ≤ a ∧ (a : ℝ) < m := by exact_mod_cast ha
    have hb' : (0 : ℝ) ≤ b ∧ (b : ℝ) < m := by exact_mod_cast hb
    have hs : (A + r * a, B + r * b) ∈
        Set.Ico (A + r * a) (A + r * (a + 1)) ×ˢ
          Set.Ico (B + r * b) (B + r * (b + 1)) := by
      simp only [Set.mem_prod, Set.mem_Ico]
      constructor <;> constructor <;> nlinarith
    have hl : (A + r * a, B + r * b) ∈
        Set.Ico A (A + r * m) ×ˢ Set.Ico B (B + r * m) := by
      simp only [Set.mem_prod, Set.mem_Ico]
      constructor <;> constructor <;> nlinarith [ha'.1, ha'.2, hb'.1, hb'.2]
    exact Set.disjoint_left.mp hdisj hs hl
  have hcorner : ¬ ((a = -1 ∨ a = m) ∧ (b = -1 ∨ b = m)) := by
    rintro ⟨ha, hb⟩
    apply hxy
    apply Prod.ext
    · rcases ha with ha | ha
      · have ha' : (a : ℝ) = -1 := by exact_mod_cast ha
        nlinarith [hx.1.1.2, hx.2.1.1, hy.1.1.2, hy.2.1.1]
      · have ha' : (a : ℝ) = m := by exact_mod_cast ha
        nlinarith [hx.1.1.1, hx.2.1.2, hy.1.1.1, hy.2.1.2]
    · rcases hb with hb | hb
      · have hb' : (b : ℝ) = -1 := by exact_mod_cast hb
        nlinarith [hx.1.2.2, hx.2.2.1, hy.1.2.2, hy.2.2.1]
      · have hb' : (b : ℝ) = m := by exact_mod_cast hb
        nlinarith [hx.1.2.1, hx.2.2.2, hy.1.2.1, hy.2.2.2]
  rcases hedge with ha | ha | hb | hb
  · exact Or.inl ⟨ha, by omega, by omega⟩
  · exact Or.inr (Or.inl ⟨ha, by omega, by omega⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hb, by omega, by omega⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hb, by omega, by omega⟩))

private theorem rectangles_contact (a b r A B R : ℝ) (hr : 0 < r) (hR : 0 < R)
    (s : Fin 4)
    (hpos : match s.val with
      | 0 => a + r = A ∧ B ≤ b ∧ b + r ≤ B + R
      | 1 => b + r = B ∧ A ≤ a ∧ a + r ≤ A + R
      | 2 => a = A + R ∧ B ≤ b ∧ b + r ≤ B + R
      | _ => b = B + R ∧ A ≤ a ∧ a + r ≤ A + R) :
    (Set.Icc a (a + r) ×ˢ Set.Icc b (b + r)) ∩
      (Set.Icc A (A + R) ×ˢ Set.Icc B (B + R)) =
    match s.val with
    | 0 => {a + r} ×ˢ Set.Icc b (b + r)
    | 1 => Set.Icc a (a + r) ×ˢ {b + r}
    | 2 => {a} ×ˢ Set.Icc b (b + r)
    | _ => Set.Icc a (a + r) ×ˢ {b} := by
  fin_cases s <;> norm_num at hpos ⊢
  · rcases hpos with ⟨he, hl, hu⟩
    ext x
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_Icc, Set.mem_singleton_iff,
      Prod.le_def]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, ⟨⟨h5, h6⟩, ⟨h7, h8⟩⟩⟩
      exact ⟨by linarith, h2, h4⟩
    · rintro ⟨hc, h1, h2⟩
      refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · rcases hpos with ⟨he, hl, hu⟩
    ext x
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_Icc, Set.mem_singleton_iff,
      Prod.le_def]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, ⟨⟨h5, h6⟩, ⟨h7, h8⟩⟩⟩
      exact ⟨⟨h1, h3⟩, by linarith⟩
    · rintro ⟨⟨h1, h2⟩, hc⟩
      refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · rcases hpos with ⟨he, hl, hu⟩
    ext x
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_Icc, Set.mem_singleton_iff,
      Prod.le_def]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, ⟨⟨h5, h6⟩, ⟨h7, h8⟩⟩⟩
      exact ⟨by linarith, h2, h4⟩
    · rintro ⟨hc, h1, h2⟩
      refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · rcases hpos with ⟨he, hl, hu⟩
    ext x
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_Icc, Set.mem_singleton_iff,
      Prod.le_def]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, ⟨⟨h5, h6⟩, ⟨h7, h8⟩⟩⟩
      exact ⟨⟨h1, h3⟩, by linarith⟩
    · rintro ⟨⟨h1, h2⟩, hc⟩
      refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

private theorem cells_contact_offsets (o : ℝ × ℝ) (ℓ j : ℕ) (z w : ℤ × ℤ)
    (m : ℤ) (hm : 0 < m) (hp : (2 : ℝ) ^ j = 2 ^ ℓ * m)
    (hdisj : Disjoint (dyadicCell o ℓ z) (dyadicCell o j w))
    (hcontact : (closure (dyadicCell o ℓ z) ∩ closure (dyadicCell o j w)).Nontrivial) :
    (z.1 - m * w.1 = -1 ∧ 0 ≤ z.2 - m * w.2 ∧ z.2 - m * w.2 < m) ∨
      (z.1 - m * w.1 = m ∧ 0 ≤ z.2 - m * w.2 ∧ z.2 - m * w.2 < m) ∨
      (z.2 - m * w.2 = -1 ∧ 0 ≤ z.1 - m * w.1 ∧ z.1 - m * w.1 < m) ∨
      (z.2 - m * w.2 = m ∧ 0 ≤ z.1 - m * w.1 ∧ z.1 - m * w.1 < m) := by
  let r := (2 : ℝ) ^ ℓ
  let A := o.1 + r * m * w.1
  let B := o.2 + r * m * w.2
  let a := z.1 - m * w.1
  let b := z.2 - m * w.2
  have hn (u : ℝ) (v t : ℤ) :
      (u + r * m * t) + r * (v - m * t : ℤ) = u + r * v ∧
        (u + r * m * t) + r * ((v - m * t : ℤ) + 1) = u + r * (v + 1) := by
    constructor <;> push_cast <;> ring
  have hl (u : ℝ) (t : ℤ) :
      (u + r * m * t) + r * m = u + (2 : ℝ) ^ j * (t + 1) := by
    rw [hp]
    dsimp [r]
    ring
  have hsCell : dyadicCell o ℓ z =
      Set.Ico (A + r * a) (A + r * (a + 1)) ×ˢ
        Set.Ico (B + r * b) (B + r * (b + 1)) := by
    dsimp [dyadicCell, A, B, a, b]
    rw [(hn o.1 z.1 w.1).1, (hn o.1 z.1 w.1).2,
      (hn o.2 z.2 w.2).1, (hn o.2 z.2 w.2).2]
  have hlCell : dyadicCell o j w =
      Set.Ico A (A + r * m) ×ˢ Set.Ico B (B + r * m) := by
    dsimp [dyadicCell, A, B]
    rw [hl o.1 w.1, hl o.2 w.2, hp]
  have hsClosure : closure (dyadicCell o ℓ z) =
      Set.Icc (A + r * a) (A + r * (a + 1)) ×ˢ
        Set.Icc (B + r * b) (B + r * (b + 1)) := by
    rw [closure_dyadicCell]
    dsimp [A, B, a, b]
    rw [(hn o.1 z.1 w.1).1, (hn o.1 z.1 w.1).2,
      (hn o.2 z.2 w.2).1, (hn o.2 z.2 w.2).2]
  have hlClosure : closure (dyadicCell o j w) =
      Set.Icc A (A + r * m) ×ˢ Set.Icc B (B + r * m) := by
    rw [closure_dyadicCell]
    dsimp [A, B]
    rw [hl o.1 w.1, hl o.2 w.2, hp]
  rw [hsCell, hlCell] at hdisj
  rw [hsClosure, hlClosure] at hcontact
  exact contact_offsets A B r (by dsimp [r]; positivity) m a b hm hdisj hcontact

private theorem midpoint_endpoints (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (s : Fin 4) (j : Fin 2) :
    (cellFanStart o ℓ z (fun _ ↦ true) ⟨s, j⟩,
      cellFanEnd o ℓ z (fun _ ↦ true) ⟨s, j⟩) =
    match s.val with
    | 0 => ((o.1 + 2 ^ ℓ * (z.1 + 1), o.2 + 2 ^ ℓ * z.2 + 2 ^ ℓ / 2 * j.val),
        (o.1 + 2 ^ ℓ * (z.1 + 1), o.2 + 2 ^ ℓ * z.2 + 2 ^ ℓ / 2 * (j.val + 1)))
    | 1 => ((o.1 + 2 ^ ℓ * (z.1 + 1) - 2 ^ ℓ / 2 * j.val,
        o.2 + 2 ^ ℓ * (z.2 + 1)),
        (o.1 + 2 ^ ℓ * (z.1 + 1) - 2 ^ ℓ / 2 * (j.val + 1),
        o.2 + 2 ^ ℓ * (z.2 + 1)))
    | 2 => ((o.1 + 2 ^ ℓ * z.1, o.2 + 2 ^ ℓ * (z.2 + 1) - 2 ^ ℓ / 2 * j.val),
        (o.1 + 2 ^ ℓ * z.1, o.2 + 2 ^ ℓ * (z.2 + 1) - 2 ^ ℓ / 2 * (j.val + 1)))
    | _ => ((o.1 + 2 ^ ℓ * z.1 + 2 ^ ℓ / 2 * j.val, o.2 + 2 ^ ℓ * z.2),
        (o.1 + 2 ^ ℓ * z.1 + 2 ^ ℓ / 2 * (j.val + 1), o.2 + 2 ^ ℓ * z.2)) := by
  fin_cases s
  · change ((o.1 + 2 ^ ℓ * z.1 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * 1,
      o.2 + 2 ^ ℓ * z.2 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * ((j.val : ℝ) - 1)),
      (o.1 + 2 ^ ℓ * z.1 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * 1,
      o.2 + 2 ^ ℓ * z.2 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * j.val)) = _
    apply Prod.ext <;> apply Prod.ext <;> norm_num <;> ring
  · change ((o.1 + 2 ^ ℓ * z.1 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * (-((j.val : ℝ) - 1)),
      o.2 + 2 ^ ℓ * z.2 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * 1),
      (o.1 + 2 ^ ℓ * z.1 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * (-(j.val : ℝ)),
      o.2 + 2 ^ ℓ * z.2 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * 1)) = _
    apply Prod.ext <;> apply Prod.ext <;> norm_num <;> ring
  · change ((o.1 + 2 ^ ℓ * z.1 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * (-1),
      o.2 + 2 ^ ℓ * z.2 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * (-((j.val : ℝ) - 1))),
      (o.1 + 2 ^ ℓ * z.1 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * (-1),
      o.2 + 2 ^ ℓ * z.2 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * (-(j.val : ℝ)))) = _
    apply Prod.ext <;> apply Prod.ext <;> norm_num <;> ring
  · change ((o.1 + 2 ^ ℓ * z.1 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * ((j.val : ℝ) - 1),
      o.2 + 2 ^ ℓ * z.2 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * (-1)),
      (o.1 + 2 ^ ℓ * z.1 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * j.val,
      o.2 + 2 ^ ℓ * z.2 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * (-1))) = _
    apply Prod.ext <;> apply Prod.ext <;> norm_num <;> ring

private theorem midpoint_side_rectangle (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (s : Fin 4) (j : Fin 2) :
    segment ℝ (cellFanStart o ℓ z (fun _ ↦ true) ⟨s, j⟩)
      (cellFanEnd o ℓ z (fun _ ↦ true) ⟨s, j⟩) =
    match s.val with
    | 0 => {o.1 + 2 ^ ℓ * (z.1 + 1)} ×ˢ
        Set.Icc (o.2 + 2 ^ ℓ * z.2 + 2 ^ ℓ / 2 * j.val)
          (o.2 + 2 ^ ℓ * z.2 + 2 ^ ℓ / 2 * (j.val + 1))
    | 1 => Set.Icc (o.1 + 2 ^ ℓ * (z.1 + 1) - 2 ^ ℓ / 2 * (j.val + 1))
        (o.1 + 2 ^ ℓ * (z.1 + 1) - 2 ^ ℓ / 2 * j.val) ×ˢ
          {o.2 + 2 ^ ℓ * (z.2 + 1)}
    | 2 => {o.1 + 2 ^ ℓ * z.1} ×ˢ
        Set.Icc (o.2 + 2 ^ ℓ * (z.2 + 1) - 2 ^ ℓ / 2 * (j.val + 1))
          (o.2 + 2 ^ ℓ * (z.2 + 1) - 2 ^ ℓ / 2 * j.val)
    | _ => Set.Icc (o.1 + 2 ^ ℓ * z.1 + 2 ^ ℓ / 2 * j.val)
        (o.1 + 2 ^ ℓ * z.1 + 2 ^ ℓ / 2 * (j.val + 1)) ×ˢ {o.2 + 2 ^ ℓ * z.2} := by
  have hs := congrArg Prod.fst (midpoint_endpoints o ℓ z s j)
  have he := congrArg Prod.snd (midpoint_endpoints o ℓ z s j)
  dsimp only at hs he
  rw [hs, he]
  have ht : 0 < (2 : ℝ) ^ ℓ := by positivity
  fin_cases s
  · exact vertical_segment _ _ _ (by linarith)
  · rw [segment_symm]
    exact horizontal_segment _ _ _ (by linarith)
  · rw [segment_symm]
    exact vertical_segment _ _ _ (by linarith)
  · exact horizontal_segment _ _ _ (by linarith)

private theorem cells_contact_side (o : ℝ × ℝ) (ℓ j : ℕ) (z w : ℤ × ℤ)
    (s : Fin 4)
    (hpos : match s.val with
      | 0 => (2 : ℝ) ^ ℓ * (z.1 + 1) = 2 ^ j * w.1 ∧
          (2 : ℝ) ^ j * w.2 ≤ 2 ^ ℓ * z.2 ∧ (2 : ℝ) ^ ℓ * (z.2 + 1) ≤ 2 ^ j * (w.2 + 1)
      | 1 => (2 : ℝ) ^ ℓ * (z.2 + 1) = 2 ^ j * w.2 ∧
          (2 : ℝ) ^ j * w.1 ≤ 2 ^ ℓ * z.1 ∧ (2 : ℝ) ^ ℓ * (z.1 + 1) ≤ 2 ^ j * (w.1 + 1)
      | 2 => (2 : ℝ) ^ ℓ * z.1 = 2 ^ j * (w.1 + 1) ∧
          (2 : ℝ) ^ j * w.2 ≤ 2 ^ ℓ * z.2 ∧ (2 : ℝ) ^ ℓ * (z.2 + 1) ≤ 2 ^ j * (w.2 + 1)
      | _ => (2 : ℝ) ^ ℓ * z.2 = 2 ^ j * (w.2 + 1) ∧
          (2 : ℝ) ^ j * w.1 ≤ 2 ^ ℓ * z.1 ∧ (2 : ℝ) ^ ℓ * (z.1 + 1) ≤ 2 ^ j * (w.1 + 1)) :
    closure (dyadicCell o ℓ z) ∩ closure (dyadicCell o j w) = dyadicCellSide o ℓ z s := by
  have hrect := rectangles_contact (o.1 + (2 : ℝ) ^ ℓ * z.1)
    (o.2 + (2 : ℝ) ^ ℓ * z.2) ((2 : ℝ) ^ ℓ)
    (o.1 + (2 : ℝ) ^ j * w.1) (o.2 + (2 : ℝ) ^ j * w.2) ((2 : ℝ) ^ j)
    (by positivity) (by positivity) s (by
      fin_cases s <;> norm_num at hpos ⊢
      all_goals
        rcases hpos with ⟨he, hl, hu⟩
        refine ⟨?_, ?_, ?_⟩ <;> nlinarith only [he, hl, hu])
  rw [closure_dyadicCell, closure_dyadicCell]
  simp only [mul_add, mul_one, ← add_assoc]
  rw [hrect, whole_side_rectangle]
  fin_cases s <;> norm_num [mul_add, ← add_assoc]

private theorem scale_interval_bounds (r : ℝ) (hr : 0 < r) (m v w : ℤ)
    (hl : 0 ≤ v - m * w) (hu : v - m * w < m) :
    r * m * w ≤ r * v ∧ r * ((v : ℝ) + 1) ≤ r * m * ((w : ℝ) + 1) := by
  have hl' : (m : ℝ) * w ≤ v := by exact_mod_cast (show m * w ≤ v by omega)
  have hu' : (v : ℝ) + 1 ≤ (m : ℝ) * ((w : ℝ) + 1) := by
    exact_mod_cast (show v + 1 ≤ m * (w + 1) by rw [mul_add, mul_one]; omega)
  constructor
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hl' hr.le
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hu' hr.le

private theorem scaled_left_touch (r : ℝ) (m v w : ℤ) (he : v - m * w = -1) :
    r * ((v : ℝ) + 1) = r * m * w := by
  have he' : (v : ℝ) + 1 = (m : ℝ) * w := by
    exact_mod_cast (show v + 1 = m * w by omega)
  rw [he']
  ring

private theorem scaled_right_touch (r : ℝ) (m v w : ℤ) (he : v - m * w = m) :
    r * v = r * m * ((w : ℝ) + 1) := by
  have he' : (v : ℝ) = (m : ℝ) * ((w : ℝ) + 1) := by
    exact_mod_cast (show v = m * (w + 1) by rw [mul_add, mul_one]; omega)
  rw [he']
  ring

private theorem contact_side_of_position (o : ℝ × ℝ) (ℓ j : ℕ) (z w : ℤ × ℤ)
    (m : ℤ) (hp : (2 : ℝ) ^ j = 2 ^ ℓ * m) (s : Fin 4)
    (hpos : match s.val with
      | 0 => z.1 - m * w.1 = -1 ∧ 0 ≤ z.2 - m * w.2 ∧ z.2 - m * w.2 < m
      | 1 => z.2 - m * w.2 = -1 ∧ 0 ≤ z.1 - m * w.1 ∧ z.1 - m * w.1 < m
      | 2 => z.1 - m * w.1 = m ∧ 0 ≤ z.2 - m * w.2 ∧ z.2 - m * w.2 < m
      | _ => z.2 - m * w.2 = m ∧ 0 ≤ z.1 - m * w.1 ∧ z.1 - m * w.1 < m) :
    closure (dyadicCell o ℓ z) ∩ closure (dyadicCell o j w) = dyadicCellSide o ℓ z s := by
  apply cells_contact_side
  have hr : 0 < (2 : ℝ) ^ ℓ := by positivity
  fin_cases s <;> norm_num at hpos ⊢
  · obtain ⟨he, hl, hu⟩ := hpos
    obtain ⟨hl', hu'⟩ := scale_interval_bounds ((2 : ℝ) ^ ℓ) hr m z.2 w.2 (by omega) hu
    simpa only [hp, mul_assoc] using
      And.intro (scaled_left_touch ((2 : ℝ) ^ ℓ) m z.1 w.1 he) (And.intro hl' hu')
  · obtain ⟨he, hl, hu⟩ := hpos
    obtain ⟨hl', hu'⟩ := scale_interval_bounds ((2 : ℝ) ^ ℓ) hr m z.1 w.1 (by omega) hu
    simpa only [hp, mul_assoc] using
      And.intro (scaled_left_touch ((2 : ℝ) ^ ℓ) m z.2 w.2 he) (And.intro hl' hu')
  · obtain ⟨he, hl, hu⟩ := hpos
    obtain ⟨hl', hu'⟩ := scale_interval_bounds ((2 : ℝ) ^ ℓ) hr m z.2 w.2 (by omega) hu
    simpa only [hp, mul_assoc] using
      And.intro (scaled_right_touch ((2 : ℝ) ^ ℓ) m z.1 w.1 he) (And.intro hl' hu')
  · obtain ⟨he, hl, hu⟩ := hpos
    obtain ⟨hl', hu'⟩ := scale_interval_bounds ((2 : ℝ) ^ ℓ) hr m z.1 w.1 (by omega) hu
    simpa only [hp, mul_assoc] using
      And.intro (scaled_right_touch ((2 : ℝ) ^ ℓ) m z.2 w.2 he) (And.intro hl' hu')

private theorem exists_binary_index (b : ℤ) (hb0 : 0 ≤ b) (hb2 : b < 2) :
    ∃ n : Fin 2, (n.val : ℤ) = b := by
  exact ⟨⟨b.toNat, by omega⟩, by simp [Int.toNat_of_nonneg hb0]⟩

private theorem opposing_side_of_position (o : ℝ × ℝ) (ℓ j : ℕ) (z w : ℤ × ℤ)
    (m : ℤ) (hscale : (m = 1 ∧ j = ℓ) ∨ (m = 2 ∧ j = ℓ + 1)) (s : Fin 4)
    (hpos : match s.val with
      | 0 => z.1 - m * w.1 = -1 ∧ 0 ≤ z.2 - m * w.2 ∧ z.2 - m * w.2 < m
      | 1 => z.2 - m * w.2 = -1 ∧ 0 ≤ z.1 - m * w.1 ∧ z.1 - m * w.1 < m
      | 2 => z.1 - m * w.1 = m ∧ 0 ≤ z.2 - m * w.2 ∧ z.2 - m * w.2 < m
      | _ => z.2 - m * w.2 = m ∧ 0 ≤ z.1 - m * w.1 ∧ z.1 - m * w.1 < m) :
    ∃ t : Fin 4, t = s + 2 ∧
      ((j = ℓ ∧ dyadicCellSide o ℓ z s = dyadicCellSide o j w t) ∨
        (j = ℓ + 1 ∧ ∃ n : Fin 2, dyadicCellSide o ℓ z s = segment ℝ
          (cellFanStart o j w (fun _ ↦ true) ⟨t, n⟩)
          (cellFanEnd o j w (fun _ ↦ true) ⟨t, n⟩))) := by
  fin_cases s <;> norm_num at hpos
  · refine ⟨2, rfl, ?_⟩
    rcases hscale with ⟨rfl, hj⟩ | ⟨rfl, hj⟩
    · subst j
      left
      refine ⟨rfl, ?_⟩
      have hN := scaled_left_touch ((2 : ℝ) ^ ℓ) 1 z.1 w.1 hpos.1
      norm_num at hN
      have hT : z.2 = w.2 := by omega
      rw [whole_side_rectangle, whole_side_rectangle]
      norm_num
      rw [hT, hN]
    · subst j
      right
      refine ⟨rfl, ?_⟩
      obtain ⟨n, hn⟩ := exists_binary_index (1 - (z.2 - 2 * w.2)) (by omega) (by omega)
      refine ⟨n, ?_⟩
      have hN := scaled_left_touch ((2 : ℝ) ^ ℓ) 2 z.1 w.1 hpos.1
      norm_num at hN
      have hT : (2 : ℝ) ^ ℓ * n.val = 2 ^ ℓ * (1 - ((z.2 : ℝ) - 2 * w.2)) := by
        congr 1
        exact_mod_cast hn
      rw [whole_side_rectangle, midpoint_side_rectangle]
      norm_num [pow_succ]
      congr 2 <;> nlinarith only [hN, hT]
  · refine ⟨3, rfl, ?_⟩
    rcases hscale with ⟨rfl, hj⟩ | ⟨rfl, hj⟩
    · subst j
      left
      refine ⟨rfl, ?_⟩
      have hN := scaled_left_touch ((2 : ℝ) ^ ℓ) 1 z.2 w.2 hpos.1
      norm_num at hN
      have hT : z.1 = w.1 := by omega
      rw [whole_side_rectangle, whole_side_rectangle]
      norm_num
      rw [hT, hN]
    · subst j
      right
      refine ⟨rfl, ?_⟩
      obtain ⟨n, hn⟩ := exists_binary_index (z.1 - 2 * w.1) (by omega) (by omega)
      refine ⟨n, ?_⟩
      have hN := scaled_left_touch ((2 : ℝ) ^ ℓ) 2 z.2 w.2 hpos.1
      norm_num at hN
      have hT : (2 : ℝ) ^ ℓ * n.val = 2 ^ ℓ * ((z.1 : ℝ) - 2 * w.1) := by
        congr 1
        exact_mod_cast hn
      rw [whole_side_rectangle, midpoint_side_rectangle]
      norm_num [pow_succ]
      congr 2 <;> nlinarith only [hN, hT]
  · refine ⟨0, rfl, ?_⟩
    rcases hscale with ⟨rfl, hj⟩ | ⟨rfl, hj⟩
    · subst j
      left
      refine ⟨rfl, ?_⟩
      have hN := scaled_right_touch ((2 : ℝ) ^ ℓ) 1 z.1 w.1 hpos.1
      norm_num at hN
      have hT : z.2 = w.2 := by omega
      rw [whole_side_rectangle, whole_side_rectangle]
      norm_num
      rw [hT, hN]
    · subst j
      right
      refine ⟨rfl, ?_⟩
      obtain ⟨n, hn⟩ := exists_binary_index (z.2 - 2 * w.2) (by omega) (by omega)
      refine ⟨n, ?_⟩
      have hN := scaled_right_touch ((2 : ℝ) ^ ℓ) 2 z.1 w.1 hpos.1
      norm_num at hN
      have hT : (2 : ℝ) ^ ℓ * n.val = 2 ^ ℓ * ((z.2 : ℝ) - 2 * w.2) := by
        congr 1
        exact_mod_cast hn
      rw [whole_side_rectangle, midpoint_side_rectangle]
      norm_num [pow_succ]
      congr 2 <;> nlinarith only [hN, hT]
  · refine ⟨1, rfl, ?_⟩
    rcases hscale with ⟨rfl, hj⟩ | ⟨rfl, hj⟩
    · subst j
      left
      refine ⟨rfl, ?_⟩
      have hN := scaled_right_touch ((2 : ℝ) ^ ℓ) 1 z.2 w.2 hpos.1
      norm_num at hN
      have hT : z.1 = w.1 := by omega
      rw [whole_side_rectangle, whole_side_rectangle]
      norm_num
      rw [hT, hN]
    · subst j
      right
      refine ⟨rfl, ?_⟩
      obtain ⟨n, hn⟩ := exists_binary_index (1 - (z.1 - 2 * w.1)) (by omega) (by omega)
      refine ⟨n, ?_⟩
      have hN := scaled_right_touch ((2 : ℝ) ^ ℓ) 2 z.2 w.2 hpos.1
      norm_num at hN
      have hT : (2 : ℝ) ^ ℓ * n.val = 2 ^ ℓ * (1 - ((z.1 : ℝ) - 2 * w.1)) := by
        congr 1
        exact_mod_cast hn
      rw [whole_side_rectangle, midpoint_side_rectangle]
      norm_num [pow_succ]
      congr 2 <;> nlinarith only [hN, hT]


private theorem cell_contact_ordered (o : ℝ × ℝ) (ℓ j : ℕ) (z w : ℤ × ℤ)
    (hj : j = ℓ ∨ j = ℓ + 1)
    (hdisj : Disjoint (dyadicCell o ℓ z) (dyadicCell o j w))
    (hcontact : (closure (dyadicCell o ℓ z) ∩ closure (dyadicCell o j w)).Nontrivial) :
    ∃ s t : Fin 4, t = s + 2 ∧
      closure (dyadicCell o ℓ z) ∩ closure (dyadicCell o j w) = dyadicCellSide o ℓ z s ∧
      ((j = ℓ ∧ dyadicCellSide o ℓ z s = dyadicCellSide o j w t) ∨
        (j = ℓ + 1 ∧ ∃ n : Fin 2, dyadicCellSide o ℓ z s = segment ℝ
          (cellFanStart o j w (fun _ ↦ true) ⟨t, n⟩)
          (cellFanEnd o j w (fun _ ↦ true) ⟨t, n⟩))) := by
  obtain ⟨m, hscale⟩ : ∃ m : ℤ, (m = 1 ∧ j = ℓ) ∨ (m = 2 ∧ j = ℓ + 1) := by
    rcases hj with hj | hj
    · exact ⟨1, Or.inl ⟨rfl, hj⟩⟩
    · exact ⟨2, Or.inr ⟨rfl, hj⟩⟩
  have hp : (2 : ℝ) ^ j = 2 ^ ℓ * m := by
    rcases hscale with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num [pow_succ]
  have hm : 0 < m := by
    rcases hscale with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> norm_num
  have hpositions := cells_contact_offsets o ℓ j z w m hm hp hdisj hcontact
  obtain ⟨s, hpos⟩ : ∃ s : Fin 4, match s.val with
      | 0 => z.1 - m * w.1 = -1 ∧ 0 ≤ z.2 - m * w.2 ∧ z.2 - m * w.2 < m
      | 1 => z.2 - m * w.2 = -1 ∧ 0 ≤ z.1 - m * w.1 ∧ z.1 - m * w.1 < m
      | 2 => z.1 - m * w.1 = m ∧ 0 ≤ z.2 - m * w.2 ∧ z.2 - m * w.2 < m
      | _ => z.2 - m * w.2 = m ∧ 0 ≤ z.1 - m * w.1 ∧ z.1 - m * w.1 < m := by
    rcases hpositions with ha | ha | hb | hb
    · exact ⟨0, by simpa using ha⟩
    · exact ⟨2, by simpa using ha⟩
    · exact ⟨1, by simpa using hb⟩
    · exact ⟨3, by simpa using hb⟩
  obtain ⟨t, ht, hopp⟩ := opposing_side_of_position o ℓ j z w m hscale s hpos
  exact ⟨s, t, ht, contact_side_of_position o ℓ j z w m hp s hpos, hopp⟩

/-- A positive-length contact between distinct actual fine cells is a whole
side of the smaller cell and a whole side or a midpoint half of the larger
cell, on opposite coordinate sides. Only the reference layer must satisfy
the late-scale bound. Source: area-law Section 11, lines 299–306 and 352–356. -/
theorem fineLayer_closedCell_contact (o : ℝ × ℝ) (k h : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (z w : ℤ × ℤ)
    (hC : 2 ≤ C) (hk : 50000000 ≤ k)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (hw : w ∈ fineLayerIndices o h (fineScaleIndex h) Z C)
    (hne : (k, z) ≠ (h, w))
    (hcontact : (closure (dyadicCell o (fineScaleIndex k) z) ∩
      closure (dyadicCell o (fineScaleIndex h) w)).Nontrivial) :
    ∃ s t : Fin 4, t = s + 2 ∧
      ((fineScaleIndex k = fineScaleIndex h ∧
          closure (dyadicCell o (fineScaleIndex k) z) ∩
            closure (dyadicCell o (fineScaleIndex h) w) = dyadicCellSide o (fineScaleIndex k) z s ∧
          dyadicCellSide o (fineScaleIndex k) z s = dyadicCellSide o (fineScaleIndex h) w t) ∨
        (fineScaleIndex h = fineScaleIndex k + 1 ∧
          closure (dyadicCell o (fineScaleIndex k) z) ∩
            closure (dyadicCell o (fineScaleIndex h) w) = dyadicCellSide o (fineScaleIndex k) z s ∧
          ∃ n : Fin 2, dyadicCellSide o (fineScaleIndex k) z s = segment ℝ
            (cellFanStart o (fineScaleIndex h) w (fun _ ↦ true) ⟨t, n⟩)
            (cellFanEnd o (fineScaleIndex h) w (fun _ ↦ true) ⟨t, n⟩)) ∨
        (fineScaleIndex k = fineScaleIndex h + 1 ∧
          closure (dyadicCell o (fineScaleIndex k) z) ∩
            closure (dyadicCell o (fineScaleIndex h) w) = dyadicCellSide o (fineScaleIndex h) w t ∧
          ∃ n : Fin 2, dyadicCellSide o (fineScaleIndex h) w t = segment ℝ
            (cellFanStart o (fineScaleIndex k) z (fun _ ↦ true) ⟨s, n⟩)
            (cellFanEnd o (fineScaleIndex k) z (fun _ ↦ true) ⟨s, n⟩))) := by
  let x := hcontact.choose.1
  have hx := hcontact.choose_fst_mem
  have hxk : x ∈ closure (dyadicLayer o k Z C) := closure_mono
    (dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices o k (fineScaleIndex k)
      Z C z (fineScaleIndex_le k) hz) hx.1
  have hxh : x ∈ closure (dyadicLayer o h Z C) := closure_mono
    (dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices o h (fineScaleIndex h)
      Z C w (fineScaleIndex_le h) hw) hx.2
  have hnear := dyadicLayer_nearby_indices o k h Z C x x hC hk hxk hxh
    (by simp only [dist_self]; positivity)
  have hlh : fineScaleIndex h ≤ fineScaleIndex k + 1 := by
    have hm := fineScaleIndex_mono hnear.1
    have hs := fineScaleIndex_succ k
    omega
  have hhl : fineScaleIndex k ≤ fineScaleIndex h + 1 := by
    have hm := fineScaleIndex_mono hnear.2
    have hs := fineScaleIndex_succ h
    omega
  have hd := fineLayer_cells_disjoint o k h Z C z w hz hw hne
  rcases le_total (fineScaleIndex k) (fineScaleIndex h) with horder | horder
  · obtain ⟨s, t, ht, hI, hopp⟩ := cell_contact_ordered o
      (fineScaleIndex k) (fineScaleIndex h) z w (by omega) hd hcontact
    refine ⟨s, t, ht, ?_⟩
    rcases hopp with ⟨he, hs⟩ | ⟨he, n, hs⟩
    · exact Or.inl ⟨he.symm, hI, hs⟩
    · exact Or.inr (Or.inl ⟨he, hI, n, hs⟩)
  · obtain ⟨s, t, ht, hI, hopp⟩ := cell_contact_ordered o
      (fineScaleIndex h) (fineScaleIndex k) w z (by omega) hd.symm
      (by simpa only [Set.inter_comm] using hcontact)
    have ht' : s = t + 2 := by
      rw [ht]
      fin_cases s <;> decide
    have hI' : closure (dyadicCell o (fineScaleIndex k) z) ∩
        closure (dyadicCell o (fineScaleIndex h) w) = dyadicCellSide o (fineScaleIndex h) w s := by
      simpa only [Set.inter_comm] using hI
    refine ⟨t, s, ht', ?_⟩
    rcases hopp with ⟨he, hs⟩ | ⟨he, n, hs⟩
    · exact Or.inl ⟨he, hI'.trans hs, hs.symm⟩
    · exact Or.inr (Or.inr ⟨he, hI', n, hs⟩)

end TNLean.PEPS.AreaLaw.Geometry

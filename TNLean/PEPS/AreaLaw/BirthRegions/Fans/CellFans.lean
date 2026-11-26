/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.BirthRegions.Layers.BeltMarks
import TNLean.PEPS.AreaLaw.Polygons.Templates.Templates
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# Triangular fans in a dyadic cell

Each side of a dyadic cell may be kept whole or divided at its midpoint.
Joining the resulting side segments to the cell center gives four to eight
closed triangles. The triangles cover the closed cell, and their common
regions are radial joins of their common perimeter points.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, lines 299–310.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.

It also contains the following results.

* `TNLean.PEPS.AreaLaw.Geometry.cellFanPolygon_base_and_radial_isAllowedSlope`: prescribed slopes of
  cell-fan edges.
* `TNLean.PEPS.AreaLaw.Geometry.cellFanPolygon_succ_inter_closedBall`: restriction of concentric
  triangular fans.
-/

section CellFans

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- A side and one of its one or two elementary segments.
Source: area-law Section 11, lines 299–310. -/
abbrev CellFanSlot (split : Fin 4 → Bool) :=
  (side : Fin 4) × Fin (if split side then 2 else 1)

/-- The center of the actual dyadic cell.
Source: area-law Section 11, lines 308–310. -/
def cellFanCenter (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ) : ℝ × ℝ :=
  (o.1 + (2 : ℝ) ^ ℓ * z.1 + (2 : ℝ) ^ ℓ / 2,
    o.2 + (2 : ℝ) ^ ℓ * z.2 + (2 : ℝ) ^ ℓ / 2)

/-- The point at tangent parameter `w` on side `side` of the square of
half-side one centered at the origin, with sides listed counterclockwise from
the right side; `w ∈ [-1, 1]` traverses the side counterclockwise.
Source: area-law Section 11, lines 299–310. -/
def cellFanSideVector (side : Fin 4) (w : ℝ) : ℝ × ℝ :=
  match side.val with
  | 0 => (1, w)
  | 1 => (-w, 1)
  | 2 => (-1, -w)
  | _ => (w, -1)

private def sidePoint (c : ℝ × ℝ) (r : ℝ) (side : Fin 4) (w : ℝ) : ℝ × ℝ :=
  c + r • cellFanSideVector side w

private def fanLower (split : Fin 4 → Bool) (i : CellFanSlot split) : ℝ :=
  if split i.1 then (i.2.val : ℝ) - 1 else -1

private def fanUpper (split : Fin 4 → Bool) (i : CellFanSlot split) : ℝ :=
  if split i.1 then (i.2.val : ℝ) else 1

/-- The first endpoint of an elementary segment, in counterclockwise order.
Source: area-law Section 11, lines 299–310. -/
def cellFanStart (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (i : CellFanSlot split) : ℝ × ℝ :=
  sidePoint (cellFanCenter o ℓ z) ((2 : ℝ) ^ ℓ / 2) i.1 (fanLower split i)

/-- The last endpoint of an elementary segment, in counterclockwise order.
Source: area-law Section 11, lines 299–310. -/
def cellFanEnd (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (i : CellFanSlot split) : ℝ × ℝ :=
  sidePoint (cellFanCenter o ℓ z) ((2 : ℝ) ^ ℓ / 2) i.1 (fanUpper split i)

/-- The start of an elementary segment in center-and-side coordinates: the
side point at tangent parameter `j - 1` of a split side and `-1` of a whole
side. Source: area-law Section 11, lines 299–310. -/
theorem cellFanStart_eq (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (i : CellFanSlot split) :
    cellFanStart o ℓ z split i = cellFanCenter o ℓ z +
      ((2 : ℝ) ^ ℓ / 2) • cellFanSideVector i.1
        (if split i.1 then (i.2.val : ℝ) - 1 else -1) := rfl

/-- The end of an elementary segment in center-and-side coordinates: the side
point at tangent parameter `j` of a split side and `1` of a whole side.
Source: area-law Section 11, lines 299–310. -/
theorem cellFanEnd_eq (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (i : CellFanSlot split) :
    cellFanEnd o ℓ z split i = cellFanCenter o ℓ z +
      ((2 : ℝ) ^ ℓ / 2) • cellFanSideVector i.1
        (if split i.1 then (i.2.val : ℝ) else 1) := rfl

private theorem fan_params_cases (split : Fin 4 → Bool) (i : CellFanSlot split) :
    (fanLower split i = -1 ∧ fanUpper split i = 1) ∨
      (fanLower split i = -1 ∧ fanUpper split i = 0) ∨
      (fanLower split i = 0 ∧ fanUpper split i = 1) := by
  rcases i with ⟨side, j⟩
  cases hs : split side
  · simp [fanLower, fanUpper, hs]
  · have hj : j.val < 2 := by simpa [hs] using j.isLt
    have hj' : j.val = 0 ∨ j.val = 1 := by omega
    rcases hj' with hj' | hj' <;> simp [fanLower, fanUpper, hs, hj']

private theorem sidePoint_segment (c : ℝ × ℝ) (r : ℝ) (side : Fin 4)
    {u v : ℝ} (huv : u < v) :
    segment ℝ (sidePoint c r side u) (sidePoint c r side v) =
      sidePoint c r side '' Set.Icc u v := by
  have haff (a : ℝ) : sidePoint c r side (u + a * (v - u)) =
      sidePoint c r side u + a • (sidePoint c r side v - sidePoint c r side u) := by
    apply Prod.ext <;> fin_cases side <;> simp [sidePoint, cellFanSideVector, smul_eq_mul] <;> ring
  rw [segment_eq_image']
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨u + a * (v - u), ⟨?_, ?_⟩, ?_⟩
    · nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr huv.le)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr huv.le)]
    · exact haff a
  · rintro ⟨w, hw, rfl⟩
    refine ⟨(w - u) / (v - u), ⟨?_, ?_⟩, ?_⟩
    · exact div_nonneg (sub_nonneg.mpr hw.1) (sub_pos.mpr huv).le
    · apply (div_le_iff₀ (sub_pos.mpr huv)).mpr
      linarith [hw.2]
    · have hd := div_mul_cancel₀ (w - u) (sub_ne_zero.mpr huv.ne')
      dsimp only
      rw [← haff, hd]
      congr 1
      ring

private theorem norm_sideVector (side : Fin 4) {w : ℝ} (hw : w ∈ Set.Icc (-1) 1) :
    ‖cellFanSideVector side w‖ = 1 := by
  have habs : |w| ≤ 1 := abs_le.mpr hw
  fin_cases side <;> simp [cellFanSideVector, Prod.norm_def, Real.norm_eq_abs,
    max_eq_left habs, max_eq_right habs]

private theorem norm_sidePoint_sub (c : ℝ × ℝ) {r : ℝ} (hr : 0 < r)
    (side : Fin 4) {w : ℝ} (hw : w ∈ Set.Icc (-1) 1) :
    ‖sidePoint c r side w - c‖ = r := by
  simp [sidePoint, norm_smul, norm_sideVector side hw, Real.norm_eq_abs, abs_of_pos hr]

/-- Every point on the actual outer base of a fan triangle lies at the
half-side distance from its center in the maximum norm.
Source: Section 11, `prop:two-families`, lines 299–323, especially 308–316,
and `geometry:initial-stars`, lines 352–363. -/
theorem norm_sub_cellFanCenter_of_mem_base (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (i : CellFanSlot split) {x : ℝ × ℝ}
    (hx : x ∈ segment ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i)) :
    ‖x - cellFanCenter o ℓ z‖ = (2 : ℝ) ^ ℓ / 2 := by
  have hp := fan_params_cases split i
  have huv : fanLower split i < fanUpper split i := by rcases hp with h | h | h <;> linarith
  rw [cellFanStart, cellFanEnd, sidePoint_segment _ _ _ huv] at hx
  obtain ⟨w, hw, rfl⟩ := hx
  apply norm_sidePoint_sub _ (div_pos (pow_pos zero_lt_two ℓ) (by norm_num))
  rcases hp with h | h | h <;> constructor <;> linarith [hw.1, hw.2]

private theorem sidePoint_of_sphere (c : ℝ × ℝ) {r : ℝ} (hr : 0 < r)
    (x : ℝ × ℝ) (hx : ‖x - c‖ = r) :
    ∃ side : Fin 4, ∃ w ∈ Set.Icc (-1 : ℝ) 1, sidePoint c r side w = x := by
  have hmax : max |x.1 - c.1| |x.2 - c.2| = r := by
    simpa [Prod.norm_def, Real.norm_eq_abs] using hx
  have hfst : |x.1 - c.1| ≤ r := (le_max_left _ _).trans hmax.le
  have hsnd : |x.2 - c.2| ≤ r := (le_max_right _ _).trans hmax.le
  have hparam {a : ℝ} (ha : |a| ≤ r) : a / r ∈ Set.Icc (-1 : ℝ) 1 := by
    apply abs_le.mp
    rw [abs_div, abs_of_pos hr]
    exact (div_le_iff₀ hr).mpr (by simpa using ha)
  have hcancel (a : ℝ) : r * (a / r) = a := by
    simpa [mul_comm] using div_mul_cancel₀ a hr.ne'
  by_cases hd : |x.2 - c.2| ≤ |x.1 - c.1|
  · have he : |x.1 - c.1| = r := by rwa [max_eq_left hd] at hmax
    by_cases hs : 0 ≤ x.1 - c.1
    · have he' : x.1 - c.1 = r := by rwa [abs_of_nonneg hs] at he
      refine ⟨0, (x.2 - c.2) / r, hparam hsnd, ?_⟩
      apply Prod.ext <;> simp [sidePoint, cellFanSideVector, smul_eq_mul, hcancel]
      all_goals linarith
    · have he' : -(x.1 - c.1) = r := by rwa [abs_of_neg (lt_of_not_ge hs)] at he
      refine ⟨2, -(x.2 - c.2) / r, hparam (by simpa only [abs_neg] using hsnd), ?_⟩
      apply Prod.ext <;> simp [sidePoint, cellFanSideVector, smul_eq_mul, hcancel]
      all_goals linarith
  · have he : |x.2 - c.2| = r := by rwa [max_eq_right (le_of_not_ge hd)] at hmax
    by_cases hs : 0 ≤ x.2 - c.2
    · have he' : x.2 - c.2 = r := by rwa [abs_of_nonneg hs] at he
      refine ⟨1, -(x.1 - c.1) / r, hparam (by simpa only [abs_neg] using hfst), ?_⟩
      apply Prod.ext <;> simp [sidePoint, cellFanSideVector, smul_eq_mul, hcancel]
      all_goals linarith
    · have he' : -(x.2 - c.2) = r := by rwa [abs_of_neg (lt_of_not_ge hs)] at he
      refine ⟨3, (x.1 - c.1) / r, hparam hfst, ?_⟩
      apply Prod.ext <;> simp [sidePoint, cellFanSideVector, smul_eq_mul, hcancel]
      all_goals linarith

private theorem outerSegments_cover (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) :
    (⋃ i : CellFanSlot split, segment ℝ (cellFanStart o ℓ z split i)
      (cellFanEnd o ℓ z split i)) =
      {x | ‖x - cellFanCenter o ℓ z‖ = (2 : ℝ) ^ ℓ / 2} := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact norm_sub_cellFanCenter_of_mem_base o ℓ z split i hi
  · intro hx
    obtain ⟨side, w, hw, rfl⟩ := sidePoint_of_sphere (cellFanCenter o ℓ z)
      (div_pos (pow_pos zero_lt_two ℓ) (by norm_num)) x hx
    cases hs : split side
    · refine Set.mem_iUnion.mpr ⟨⟨side, ⟨0, by simp [hs]⟩⟩, ?_⟩
      simp only [cellFanStart, cellFanEnd, fanLower, fanUpper, hs, Bool.false_eq_true,
        ↓reduceIte]
      rw [sidePoint_segment _ _ _ (by norm_num)]
      exact ⟨w, hw, rfl⟩
    · by_cases hw0 : w ≤ 0
      · refine Set.mem_iUnion.mpr ⟨⟨side, ⟨0, by simp [hs]⟩⟩, ?_⟩
        simp only [cellFanStart, cellFanEnd, fanLower, fanUpper, hs, ↓reduceIte,
          Nat.cast_zero, zero_sub]
        rw [sidePoint_segment _ _ _ (by norm_num)]
        exact ⟨w, ⟨hw.1, hw0⟩, rfl⟩
      · refine Set.mem_iUnion.mpr ⟨⟨side, ⟨1, by simp [hs]⟩⟩, ?_⟩
        simp only [cellFanStart, cellFanEnd, fanLower, fanUpper, hs, ↓reduceIte,
          Nat.cast_one, sub_self]
        rw [sidePoint_segment _ _ _ (by norm_num)]
        exact ⟨w, ⟨(lt_of_not_ge hw0).le, hw.2⟩, rfl⟩

private theorem radial_join_sphere (c : ℝ × ℝ) {r : ℝ} (hr : 0 < r) :
    convexJoin ℝ {c} {x | ‖x - c‖ = r} = {x | ‖x - c‖ ≤ r} := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha, b, hb, hseg⟩ := mem_convexJoin.mp hx
    have ha' : a = c := ha
    subst a
    rw [segment_eq_image'] at hseg
    obtain ⟨t, ht, rfl⟩ := hseg
    simp only [Set.mem_ofPred_eq] at hb ⊢
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1, hb]
    nlinarith [ht.2]
  · intro hx
    by_cases hxc : x = c
    · subst x
      have hboundary : ‖sidePoint c r 0 0 - c‖ = r :=
        norm_sidePoint_sub c hr 0 (by norm_num)
      exact mem_convexJoin.mpr ⟨c, rfl, sidePoint c r 0 0, hboundary,
        left_mem_segment ℝ _ _⟩
    · have hd : 0 < ‖x - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxc)
      let b := c + (r / ‖x - c‖) • (x - c)
      have hb : ‖b - c‖ = r := by
        dsimp [b]
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos (div_pos hr hd), div_mul_cancel₀ _ hd.ne']
      apply mem_convexJoin.mpr
      refine ⟨c, rfl, b, hb, ?_⟩
      rw [segment_eq_image']
      refine ⟨‖x - c‖ / r, ⟨(div_pos hd hr).le, (div_le_iff₀ hr).mpr (by simpa using hx)⟩, ?_⟩
      dsimp [b]
      rw [add_sub_cancel_left, smul_smul]
      have he : ‖x - c‖ / r * (r / ‖x - c‖) = 1 := by field_simp
      rw [he, one_smul]
      abel

private theorem radial_join_inter (c : ℝ × ℝ) {r : ℝ} (hr : 0 < r)
    (S T : Set (ℝ × ℝ)) (hS : ∀ u ∈ S, ‖u - c‖ = r)
    (hT : ∀ v ∈ T, ‖v - c‖ = r) (hSne : S.Nonempty) (hTne : T.Nonempty) :
    convexJoin ℝ {c} S ∩ convexJoin ℝ {c} T =
      {c} ∪ convexJoin ℝ {c} (S ∩ T) := by
  ext p
  constructor
  · intro hp
    by_cases hpc : p = c
    · exact Or.inl hpc
    · obtain ⟨a₀, ha₀, u, hu, hpu⟩ := mem_convexJoin.mp hp.1
      obtain ⟨b₀, hb₀, v, hv, hpv⟩ := mem_convexJoin.mp hp.2
      have ha₀' : a₀ = c := ha₀
      have hb₀' : b₀ = c := hb₀
      subst a₀ b₀
      rw [segment_eq_image'] at hpu hpv
      obtain ⟨a, ha, hea⟩ := hpu
      obtain ⟨b, hb, heb⟩ := hpv
      have hea' : p - c = a • (u - c) := by rw [← hea]; dsimp only; abel
      have heb' : p - c = b • (v - c) := by rw [← heb]; dsimp only; abel
      have hna : ‖p - c‖ = a * r := by
        rw [hea', norm_smul, Real.norm_eq_abs, abs_of_nonneg ha.1, hS u hu]
      have hnb : ‖p - c‖ = b * r := by
        rw [heb', norm_smul, Real.norm_eq_abs, abs_of_nonneg hb.1, hT v hv]
      have hab : a = b := by nlinarith
      have ha0 : a ≠ 0 := by
        intro ha0
        apply hpc
        apply sub_eq_zero.mp
        simpa [ha0] using hea'
      have huv : u = v := by
        apply sub_left_injective (b := c)
        apply (smul_right_injective (M := ℝ × ℝ) ha0)
        dsimp only
        rw [← hea', hab, ← heb']
      subst v
      exact Or.inr (mem_convexJoin.mpr ⟨c, rfl, u, ⟨hu, hv⟩,
        (segment_eq_image' ℝ c u).symm ▸ ⟨a, ha, hea⟩⟩)
  · intro hp
    rcases hp with hp | hp
    · have hp' : p = c := hp
      subst p
      obtain ⟨u, hu⟩ := hSne
      obtain ⟨v, hv⟩ := hTne
      exact ⟨mem_convexJoin.mpr ⟨c, rfl, u, hu, left_mem_segment ℝ _ _⟩,
        mem_convexJoin.mpr ⟨c, rfl, v, hv, left_mem_segment ℝ _ _⟩⟩
    · obtain ⟨a, ha, u, hu, hseg⟩ := mem_convexJoin.mp hp
      exact ⟨mem_convexJoin.mpr ⟨a, ha, u, hu.1, hseg⟩,
        mem_convexJoin.mpr ⟨a, ha, u, hu.2, hseg⟩⟩

private theorem sidePoint_noncollinear (c : ℝ × ℝ) {r : ℝ} (hr : 0 < r)
    (side : Fin 4) {u v : ℝ} (huv : u < v) :
    ((sidePoint c r side u).1 - c.1) * ((sidePoint c r side v).2 - c.2) -
      ((sidePoint c r side u).2 - c.2) * ((sidePoint c r side v).1 - c.1) ≠ 0 := by
  have he : ((sidePoint c r side u).1 - c.1) * ((sidePoint c r side v).2 - c.2) -
      ((sidePoint c r side u).2 - c.2) * ((sidePoint c r side v).1 - c.1) =
      r ^ 2 * (v - u) := by
    fin_cases side <;> simp [sidePoint, cellFanSideVector, smul_eq_mul] <;> ring
  rw [he]
  exact mul_ne_zero (pow_ne_zero _ hr.ne') (sub_ne_zero.mpr huv.ne')

private theorem sidePoint_radial_allowed (c : ℝ × ℝ) (r : ℝ) (side : Fin 4)
    {w : ℝ} (hw : w = -1 ∨ w = 0 ∨ w = 1) :
    IsAllowedSlope (sidePoint c r side w - c) ∧
      IsAllowedSlope (c - sidePoint c r side w) := by
  rcases hw with rfl | rfl | rfl <;> fin_cases side <;>
    simp [sidePoint, cellFanSideVector, IsAllowedSlope, smul_eq_mul]

private theorem sidePoint_edge_allowed (c : ℝ × ℝ) (r : ℝ) (side : Fin 4) (u v : ℝ) :
    IsAllowedSlope (sidePoint c r side v - sidePoint c r side u) := by
  fin_cases side <;> simp [sidePoint, cellFanSideVector, IsAllowedSlope]

/-- The actual triangle joining the cell center to one elementary side segment.
All three edges have horizontal, vertical or diagonal slope.
Source: area-law Section 11, lines 299–310. -/
def cellFanPolygon (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (i : CellFanSlot split) : TemplatePolygon := by
  have hp := fan_params_cases split i
  have hr : 0 < (2 : ℝ) ^ ℓ / 2 := div_pos (pow_pos zero_lt_two ℓ) (by norm_num)
  have huv : fanLower split i < fanUpper split i := by rcases hp with h | h | h <;> linarith
  have hl : fanLower split i = -1 ∨ fanLower split i = 0 ∨ fanLower split i = 1 := by
    rcases hp with h | h | h <;> simp [h.1]
  have hu : fanUpper split i = -1 ∨ fanUpper split i = 0 ∨ fanUpper split i = 1 := by
    rcases hp with h | h | h <;> simp [h.2]
  exact .triangle (cellFanCenter o ℓ z) (cellFanStart o ℓ z split i)
    (cellFanEnd o ℓ z split i)
    (sidePoint_noncollinear _ hr _ huv)
    (sidePoint_radial_allowed _ _ _ hl).1
    (sidePoint_edge_allowed _ _ _ _ _)
    (sidePoint_radial_allowed _ _ _ hu).2

private theorem polygon_region_eq (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (i : CellFanSlot split) :
    (cellFanPolygon o ℓ z split i).region = convexJoin ℝ {cellFanCenter o ℓ z}
      (segment ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i)) := by
  change convexHull ℝ {cellFanCenter o ℓ z, cellFanStart o ℓ z split i,
    cellFanEnd o ℓ z split i} = _
  exact (convexJoin_singleton_segment _ _ _).symm

private theorem cell_norm_ball (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ) :
    {x | ‖x - cellFanCenter o ℓ z‖ ≤ (2 : ℝ) ^ ℓ / 2} = closure (dyadicCell o ℓ z) := by
  rw [closure_dyadicCell]
  ext x
  simp only [Set.mem_ofPred_eq, Prod.norm_def, Real.norm_eq_abs, max_le_iff, abs_le,
    Set.mem_prod, Set.mem_Icc]
  dsimp [cellFanCenter]
  constructor <;> intro h <;> constructor <;> constructor <;>
    nlinarith [h.1.1, h.1.2, h.2.1, h.2.2]

/-- The closed maximum-norm ball about a dyadic cell center is its closure.
The maximum norm is the usual product norm on `ℝ × ℝ`.

Auxiliary to OpenAI, *A two-dimensional area law from a global spectral gap*,
Section 11, `prop:two-families`, lines 299–310, and `geometry:initial-stars`,
lines 333–370, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
This is the coordinate description already used in the cell-fan cover. -/
theorem closedBall_cellFanCenter_eq_closure_dyadicCell
    (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ) :
    Metric.closedBall (cellFanCenter o ℓ z) ((2 : ℝ) ^ ℓ / 2) =
      closure (dyadicCell o ℓ z) := by
  simpa only [Metric.closedBall, dist_eq_norm] using cell_norm_ball o ℓ z

/-- A cell fan has at least four and at most eight triangles.
Source: area-law Section 11, lines 299–310. -/
theorem card_cellFanSlot_bounds (split : Fin 4 → Bool) :
    4 ≤ Fintype.card (CellFanSlot split) ∧ Fintype.card (CellFanSlot split) ≤ 8 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  constructor
  · calc
      4 = ∑ _side : Fin 4, 1 := by simp
      _ ≤ ∑ side : Fin 4, if split side then 2 else 1 :=
        Finset.sum_le_sum (fun side _ => by split <;> norm_num)
  · calc
      (∑ side : Fin 4, if split side then 2 else 1) ≤ ∑ _side : Fin 4, 2 :=
        Finset.sum_le_sum (fun side _ => by split <;> norm_num)
      _ = 8 := by simp

/-- The actual triangular fan covers precisely the closed dyadic cell.
Source: area-law Section 11, lines 299–310. -/
theorem cellFanPolygons_cover (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) :
    (⋃ i : CellFanSlot split, (cellFanPolygon o ℓ z split i).region) =
      closure (dyadicCell o ℓ z) := by
  simp_rw [polygon_region_eq, ← convexJoin_iUnion_right]
  rw [outerSegments_cover, radial_join_sphere _
    (div_pos (pow_pos zero_lt_two ℓ) (by norm_num)), cell_norm_ball]

/-- Two fan triangles share exactly the radial joins of their common perimeter
points, together with the center. This includes coincident triangles.
Source: area-law Section 11, lines 299–310. -/
theorem cellFanPolygons_inter_eq (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (i j : CellFanSlot split) :
    (cellFanPolygon o ℓ z split i).region ∩ (cellFanPolygon o ℓ z split j).region =
      {cellFanCenter o ℓ z} ∪ convexJoin ℝ {cellFanCenter o ℓ z}
        (segment ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i) ∩
          segment ℝ (cellFanStart o ℓ z split j) (cellFanEnd o ℓ z split j)) := by
  rw [polygon_region_eq, polygon_region_eq]
  apply radial_join_inter (cellFanCenter o ℓ z)
    (r := (2 : ℝ) ^ ℓ / 2) (div_pos (pow_pos zero_lt_two ℓ) (by norm_num))
  · exact fun _ hx => norm_sub_cellFanCenter_of_mem_base o ℓ z split i hx
  · exact fun _ hx => norm_sub_cellFanCenter_of_mem_base o ℓ z split j hx
  · exact ⟨_, left_mem_segment ℝ _ _⟩
  · exact ⟨_, left_mem_segment ℝ _ _⟩

private theorem sidePoint_mem_beltCellMarks (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (side : Fin 4) {w : ℝ} (hw : w = -1 ∨ w = 0 ∨ w = 1) :
    sidePoint (cellFanCenter o ℓ z) ((2 : ℝ) ^ ℓ / 2) side w ∈ beltCellMarks o ℓ z := by
  classical
  have hmark (m : Fin 3) :
      sidePoint (cellFanCenter o ℓ z) ((2 : ℝ) ^ ℓ / 2) side ((m.val : ℝ) - 1) ∈
        beltCellMarks o ℓ z := by
    let p : Fin 3 × Fin 3 := match side.val with
      | 0 => (2, m)
      | 1 => (2 - m, 2)
      | 2 => (0, 2 - m)
      | _ => (m, 0)
    apply Finset.mem_image.mpr
    refine ⟨p, Finset.mem_univ _, ?_⟩
    fin_cases side <;> fin_cases m <;> apply Prod.ext <;>
      norm_num [p, sidePoint, cellFanSideVector, cellFanCenter, smul_eq_mul] <;> ring
  rcases hw with rfl | rfl | rfl
  · simpa using hmark 0
  · simpa using hmark 1
  · convert hmark 2 using 1; norm_num

/-- The actual center and all elementary-segment endpoints are among the nine
marks of the same cell.
Source: area-law Section 11, lines 299–310 and 325–330. -/
theorem cellFan_vertices_mem_beltCellMarks (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) :
    cellFanCenter o ℓ z ∈ beltCellMarks o ℓ z ∧ ∀ i : CellFanSlot split,
      cellFanStart o ℓ z split i ∈ beltCellMarks o ℓ z ∧
      cellFanEnd o ℓ z split i ∈ beltCellMarks o ℓ z := by
  classical
  constructor
  · apply Finset.mem_image.mpr
    refine ⟨(1, 1), Finset.mem_univ _, ?_⟩
    apply Prod.ext <;> simp [cellFanCenter]
  · intro i
    have hp := fan_params_cases split i
    constructor
    · apply sidePoint_mem_beltCellMarks
      rcases hp with h | h | h <;> simp [h.1]
    · apply sidePoint_mem_beltCellMarks
      rcases hp with h | h | h <;> simp [h.2]

end TNLean.PEPS.AreaLaw.Geometry

end

end CellFans

namespace TNLean.PEPS.AreaLaw.Geometry

section CellFanSlopes

/-!
## Prescribed slopes of cell-fan edges

The elementary perimeter edge and the radial edge from its final endpoint
to the center have one of the four prescribed slopes. The assertion concerns
the existing actual fan and permits every optional midpoint subdivision.
The origin, dyadic exponent and signed cell index are arbitrary.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `prop:two-families`,
lines 308–310, and `geometry:initial-stars`, lines 352–359.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

/-- The base and last radial edge have the slopes carried by the actual
triangle constructor. Auxiliary to Section 11, `prop:two-families`,
lines 308–310, and `geometry:initial-stars`, lines 352–359. -/
private theorem triangle_base_and_last_slopes (P : TemplatePolygon) :
    match P with
    | .triangle a b c _ _ _ _ => IsAllowedSlope (c - b) ∧ IsAllowedSlope (a - c)
    | .rectangle _ _ _ _ _ _ _ _ => True := by
  cases P with
  | triangle _ _ _ _ _ hbc hca => exact ⟨hbc, hca⟩
  | rectangle => trivial

/-- The elementary base and the final radial edge of an actual fan triangle
have allowed slopes. Source: area-law Section 11,
`prop:two-families`, lines 308–310, and `geometry:initial-stars`, lines 352–359. -/
theorem cellFanPolygon_base_and_radial_isAllowedSlope
    (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (i : CellFanSlot split) :
    IsAllowedSlope (cellFanEnd o ℓ z split i - cellFanStart o ℓ z split i) ∧
      IsAllowedSlope (cellFanCenter o ℓ z - cellFanEnd o ℓ z split i) := by
  exact triangle_base_and_last_slopes (cellFanPolygon o ℓ z split i)

end CellFanSlopes

section ConcentricFans

/-!
## Restriction of concentric triangular fans

Two concentric dyadic squares with consecutive exponents have corresponding
fan triangles for every optional midpoint subdivision. Intersecting a triangle
of the larger fan with the smaller closed square gives the corresponding
triangle of the smaller fan. The metric on the plane is the maximum norm.

The smaller triangle is the image of the larger triangle under the homothety
of ratio one half about their common center. Every point of the larger base
has the same distance from that center, so clipping restricts its radial
coefficient to the interval from zero to one half.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:initial-stars`, lines 333–370,
especially 352–363, and `prop:two-families`, lines 299–323.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

/-- A triangle with its base at constant distance `2 * r` from its center
restricts to its image under the homothety of ratio one half.
Auxiliary to Section 11, `geometry:initial-stars`, lines 333–370, especially
352–363, and the actual fan construction in `prop:two-families`, lines 299–323. -/
private theorem radial_triangle_inter_closedBall (c a b : ℝ × ℝ) (r : ℝ)
    (hr : 0 < r) (hbase : ∀ y ∈ segment ℝ a b, dist c y = 2 * r) :
    convexHull ℝ {c, a, b} ∩ Metric.closedBall c r =
      (AffineMap.homothety c (1 / 2 : ℝ)) '' convexHull ℝ {c, a, b} := by
  simp only [← convexJoin_singleton_segment]
  ext x
  constructor
  · rintro ⟨hx, hball⟩
    obtain ⟨v, hv, y, hy, hxy⟩ := mem_convexJoin.mp hx
    have hvc : v = c := Set.mem_singleton_iff.mp hv
    subst v
    rw [segment_eq_image_lineMap] at hxy
    obtain ⟨u, hu, rfl⟩ := hxy
    have hd : u * (2 * r) ≤ r := by
      have hd := Metric.mem_closedBall.mp hball
      rw [dist_lineMap_left, Real.norm_eq_abs, abs_of_nonneg hu.1, hbase y hy] at hd
      exact hd
    have hu' : 2 * u ≤ 1 := by
      apply (mul_le_mul_iff_left₀ hr).mp
      nlinarith [hd]
    refine ⟨AffineMap.lineMap c y (2 * u), ?_, ?_⟩
    · exact mem_convexJoin.mpr ⟨c, by simp, y, hy,
        lineMap_mem_segment ℝ c y ⟨by linarith [hu.1], hu'⟩⟩
    · rw [AffineMap.homothety_eq_lineMap, AffineMap.lineMap_lineMap_right]
      congr 1
      ring
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨v, hv, z, hz, hyz⟩ := mem_convexJoin.mp hy
    have hvc : v = c := Set.mem_singleton_iff.mp hv
    subst v
    rw [segment_eq_image_lineMap] at hyz
    obtain ⟨u, hu, rfl⟩ := hyz
    have hu' : (1 / 2 : ℝ) * u ∈ Set.Icc 0 1 :=
      ⟨mul_nonneg (by norm_num) hu.1, by linarith [hu.2]⟩
    simp only [AffineMap.homothety_eq_lineMap, AffineMap.lineMap_lineMap_right]
    refine ⟨mem_convexJoin.mpr ⟨c, by simp, z, hz,
      lineMap_mem_segment ℝ c z hu'⟩, ?_⟩
    apply Metric.mem_closedBall.mpr
    rw [dist_lineMap_left, Real.norm_eq_abs, abs_of_nonneg hu'.1, hbase z hz]
    nlinarith [mul_le_mul_of_nonneg_right hu.2 hr.le]

/-- The actual small and large dyadic squares have the prescribed common center.
Auxiliary to Section 11, `geometry:initial-stars`, lines 352–363, and the fan
construction in `prop:two-families`, lines 299–323. -/
private theorem concentric_centers (c : ℝ × ℝ) (ℓ : ℕ) :
    let r := (2 : ℝ) ^ ℓ / 2
    cellFanCenter (c.1 - r, c.2 - r) ℓ (0, 0) = c ∧
      cellFanCenter (c.1 - 2 * r, c.2 - 2 * r) (ℓ + 1) (0, 0) = c := by
  dsimp only
  constructor <;> apply Prod.ext <;> simp [cellFanCenter, pow_succ] <;> ring

/-- Halving the displacement from the center halves the dyadic radius.
Auxiliary to Section 11, `geometry:initial-stars`, lines 352–363, and the fan
construction in `prop:two-families`, lines 299–323. -/
private theorem homothety_half_add (c v : ℝ × ℝ) (ℓ : ℕ) :
    AffineMap.homothety c (1 / 2 : ℝ) (c + ((2 : ℝ) ^ (ℓ + 1) / 2) • v) =
      c + ((2 : ℝ) ^ ℓ / 2) • v := by
  simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add,
    add_sub_cancel_left, smul_smul]
  have h : (1 / 2 : ℝ) * ((2 : ℝ) ^ (ℓ + 1) / 2) = (2 : ℝ) ^ ℓ / 2 := by
    rw [pow_succ]
    ring
  rw [h, add_comm]

/-- The corresponding actual fan endpoints are related by the same homothety,
without changing their side or optional midpoint slot.
Auxiliary to Section 11, `geometry:initial-stars`, lines 352–363, and the fan
construction in `prop:two-families`, lines 299–323. -/
private theorem concentric_endpoints (c : ℝ × ℝ) (ℓ : ℕ)
    (split : Fin 4 → Bool) (i : CellFanSlot split) :
    let r := (2 : ℝ) ^ ℓ / 2
    let oSmall := (c.1 - r, c.2 - r)
    let oLarge := (c.1 - 2 * r, c.2 - 2 * r)
    AffineMap.homothety c (1 / 2 : ℝ) (cellFanStart oLarge (ℓ + 1) (0, 0) split i) =
        cellFanStart oSmall ℓ (0, 0) split i ∧
      AffineMap.homothety c (1 / 2 : ℝ) (cellFanEnd oLarge (ℓ + 1) (0, 0) split i) =
        cellFanEnd oSmall ℓ (0, 0) split i := by
  dsimp only
  obtain ⟨hs, hl⟩ := concentric_centers c ℓ
  constructor
  · unfold cellFanStart
    rw [hs, hl]
    exact homothety_half_add c _ ℓ
  · unfold cellFanEnd
    rw [hs, hl]
    exact homothety_half_add c _ ℓ

/-- Clipping a concentric larger fan triangle by the smaller closed square
gives exactly the corresponding smaller actual triangle, for every optional
midpoint mask and slot. Source: Section 11, `geometry:initial-stars`, lines
333–370, especially 352–363, and `prop:two-families`, lines 299–323. -/
theorem cellFanPolygon_succ_inter_closedBall (c : ℝ × ℝ) (ℓ : ℕ)
    (split : Fin 4 → Bool) (i : CellFanSlot split) :
    let r := (2 : ℝ) ^ ℓ / 2
    let oSmall := (c.1 - r, c.2 - r)
    let oLarge := (c.1 - 2 * r, c.2 - 2 * r)
    (cellFanPolygon oLarge (ℓ + 1) (0, 0) split i).region ∩
        Metric.closedBall c r =
      (cellFanPolygon oSmall ℓ (0, 0) split i).region := by
  dsimp only
  let r := (2 : ℝ) ^ ℓ / 2
  let oSmall := (c.1 - r, c.2 - r)
  let oLarge := (c.1 - 2 * r, c.2 - 2 * r)
  change (cellFanPolygon oLarge (ℓ + 1) (0, 0) split i).region ∩
    Metric.closedBall c r = (cellFanPolygon oSmall ℓ (0, 0) split i).region
  have hr : 0 < r := div_pos (pow_pos zero_lt_two ℓ) (by norm_num)
  obtain ⟨hs, hl⟩ := concentric_centers c ℓ
  obtain ⟨ha, hb⟩ := concentric_endpoints c ℓ split i
  change AffineMap.homothety c (1 / 2 : ℝ)
    (cellFanStart oLarge (ℓ + 1) (0, 0) split i) = cellFanStart oSmall ℓ (0, 0) split i at ha
  change AffineMap.homothety c (1 / 2 : ℝ)
    (cellFanEnd oLarge (ℓ + 1) (0, 0) split i) = cellFanEnd oSmall ℓ (0, 0) split i at hb
  have hbase : ∀ y ∈ segment ℝ (cellFanStart oLarge (ℓ + 1) (0, 0) split i)
      (cellFanEnd oLarge (ℓ + 1) (0, 0) split i), dist c y = 2 * r := by
    intro y hy
    have hn := norm_sub_cellFanCenter_of_mem_base oLarge (ℓ + 1) (0, 0) split i hy
    rw [hl] at hn
    calc
      dist c y = ‖y - c‖ := by rw [dist_comm, dist_eq_norm]
      _ = (2 : ℝ) ^ (ℓ + 1) / 2 := hn
      _ = 2 * r := by dsimp [r]; rw [pow_succ]; ring
  change convexHull ℝ {cellFanCenter oLarge (ℓ + 1) (0, 0),
    cellFanStart oLarge (ℓ + 1) (0, 0) split i,
    cellFanEnd oLarge (ℓ + 1) (0, 0) split i} ∩ Metric.closedBall c r =
      convexHull ℝ {cellFanCenter oSmall ℓ (0, 0),
        cellFanStart oSmall ℓ (0, 0) split i, cellFanEnd oSmall ℓ (0, 0) split i}
  rw [hl, hs, radial_triangle_inter_closedBall c _ _ r hr hbase,
    (AffineMap.homothety c (1 / 2 : ℝ)).image_convexHull]
  simp only [Set.image_insert_eq, Set.image_singleton,
    AffineMap.homothety_apply_same, ha, hb]

end ConcentricFans

end TNLean.PEPS.AreaLaw.Geometry

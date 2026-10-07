/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.CellContacts
import TNLean.PEPS.AreaLaw.Geometry.SideSubdivisionMask
import Mathlib.Analysis.Normed.Affine.Convex

/-!
# Matching actual elementary sides

Every elementary segment of an actual fine cell which has positive-length
contact with another actual fine cell is the elementary segment of that
other cell, with the opposite orientation. The midpoint choices are those
determined by actual corners at or above the starting layer.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, lines 299–306.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

/-
Original formalization from the cited manuscript;
no upstream Lean proof text reused.
Manuscript: OpenAI, A two-dimensional area law from a global spectral gap,
September 24, 2026.
Pinned source: adc7f1241b42e322a6451854ab7e4b4c146bf78a
Manuscript path:
preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/10-geometry.tex

Provenance-ID: 8758-tnlean.peps.arealaw.geometry.elementary_contact_match
Downstream declaration:
TNLean.PEPS.AreaLaw.Geometry.fineLayer_elementary_contact_match
Source labels: prop:two-families, geometry:initial-stars
Source: Section 11, lines 299–306 and 352–356.

OpenAI Codex (GPT-6) assistance was used in this formalization.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

private def sideVector (s : Fin 4) (u : ℝ) : ℝ × ℝ :=
  match s.val with
  | 0 => (1, u)
  | 1 => (-u, 1)
  | 2 => (-1, -u)
  | _ => (u, -1)

private def tangent (s : Fin 4) : (ℝ × ℝ) →ᵃ[ℝ] ℝ :=
  match s.val with
  | 0 => AffineMap.snd
  | 1 => -AffineMap.fst
  | 2 => -AffineMap.snd
  | _ => AffineMap.fst

private def normal (s : Fin 4) : (ℝ × ℝ) →ᵃ[ℝ] ℝ :=
  if s.val % 2 = 0 then AffineMap.fst else AffineMap.snd

private def normalSign (s : Fin 4) : ℝ := if s.val < 2 then 1 else -1

private theorem tangent_sidePoint (c : ℝ × ℝ) (r : ℝ) (s : Fin 4) (u : ℝ) :
    tangent s (c + r • sideVector s u) = tangent s c + r * u := by
  fin_cases s <;> norm_num [tangent, sideVector] <;> ring

private theorem normal_sidePoint (c : ℝ × ℝ) (r : ℝ) (s : Fin 4) (u : ℝ) :
    normal s (c + r • sideVector s u) = normal s c + r * normalSign s := by
  fin_cases s <;> norm_num [normal, normalSign, sideVector]

private theorem tangent_normal_injective (s : Fin 4) {x y : ℝ × ℝ}
    (hn : normal s x = normal s y) (ht : tangent s x = tangent s y) : x = y := by
  fin_cases s <;> apply Prod.ext <;> norm_num [normal, tangent] at hn ht ⊢ <;> linarith

private theorem tangent_opposite (s : Fin 4) : tangent (s + 2) = -tangent s := by
  fin_cases s <;> ext x <;> norm_num [tangent]

private theorem normal_endpoints (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (i : CellFanSlot split) :
    normal i.1 (cellFanStart o ℓ z split i) =
        normal i.1 (cellFanCenter o ℓ z) + (2 : ℝ) ^ ℓ / 2 * normalSign i.1 ∧
      normal i.1 (cellFanEnd o ℓ z split i) =
        normal i.1 (cellFanCenter o ℓ z) + (2 : ℝ) ^ ℓ / 2 * normalSign i.1 := by
  constructor
  · change normal i.1 (cellFanCenter o ℓ z + ((2 : ℝ) ^ ℓ / 2) •
      sideVector i.1 (if split i.1 then (i.2.val : ℝ) - 1 else -1)) = _
    exact normal_sidePoint _ _ _ _
  · change normal i.1 (cellFanCenter o ℓ z + ((2 : ℝ) ^ ℓ / 2) •
      sideVector i.1 (if split i.1 then (i.2.val : ℝ) else 1)) = _
    exact normal_sidePoint _ _ _ _

private theorem tangent_endpoints (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (i : CellFanSlot split) :
    tangent i.1 (cellFanStart o ℓ z split i) = tangent i.1 (cellFanCenter o ℓ z) +
        (2 : ℝ) ^ ℓ / 2 * (if split i.1 then (i.2.val : ℝ) - 1 else -1) ∧
      tangent i.1 (cellFanEnd o ℓ z split i) = tangent i.1 (cellFanCenter o ℓ z) +
        (2 : ℝ) ^ ℓ / 2 * (if split i.1 then (i.2.val : ℝ) else 1) := by
  constructor
  · change tangent i.1 (cellFanCenter o ℓ z + ((2 : ℝ) ^ ℓ / 2) •
      sideVector i.1 (if split i.1 then (i.2.val : ℝ) - 1 else -1)) = _
    exact tangent_sidePoint _ _ _ _
  · change tangent i.1 (cellFanCenter o ℓ z + ((2 : ℝ) ^ ℓ / 2) •
      sideVector i.1 (if split i.1 then (i.2.val : ℝ) else 1)) = _
    exact tangent_sidePoint _ _ _ _

private theorem tangent_start_lt_end (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (i : CellFanSlot split) :
    tangent i.1 (cellFanStart o ℓ z split i) <
      tangent i.1 (cellFanEnd o ℓ z split i) := by
  obtain ⟨ha, hb⟩ := tangent_endpoints o ℓ z split i
  rw [ha, hb]
  have hq : 0 < (2 : ℝ) ^ ℓ / 2 := by positivity
  split_ifs <;> linarith

private theorem normal_mem_segment (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (i : CellFanSlot split) {x : ℝ × ℝ}
    (hx : x ∈ segment ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i)) :
    normal i.1 x = normal i.1 (cellFanCenter o ℓ z) +
      (2 : ℝ) ^ ℓ / 2 * normalSign i.1 := by
  have hx' := Set.mem_image_of_mem (normal i.1) hx
  rw [image_segment, (normal_endpoints o ℓ z split i).1,
    (normal_endpoints o ℓ z split i).2] at hx'
  simpa using hx'

private theorem endpoints_reversed (o : ℝ × ℝ) (ℓ j : ℕ) (z w : ℤ × ℤ)
    (split split' : Fin 4 → Bool) (i : CellFanSlot split) (n : CellFanSlot split')
    (hop : n.1 = i.1 + 2)
    (heq : segment ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i) =
      segment ℝ (cellFanStart o j w split' n) (cellFanEnd o j w split' n)) :
    cellFanStart o ℓ z split i = cellFanEnd o j w split' n ∧
      cellFanEnd o ℓ z split i = cellFanStart o j w split' n := by
  have hi := tangent_start_lt_end o ℓ z split i
  have hn := tangent_start_lt_end o j w split' n
  rw [hop, tangent_opposite] at hn
  change -tangent i.1 (cellFanStart o j w split' n) <
    -tangent i.1 (cellFanEnd o j w split' n) at hn
  have hn' : tangent i.1 (cellFanEnd o j w split' n) <
      tangent i.1 (cellFanStart o j w split' n) := by linarith
  have hp := congrArg (Set.image (tangent i.1)) heq
  rw [image_segment, image_segment, segment_eq_Icc hi.le,
    segment_symm, segment_eq_Icc hn'.le] at hp
  obtain ⟨ha, hb⟩ := (Set.Icc_eq_Icc_iff hi.le).mp hp
  have hna : cellFanEnd o j w split' n ∈
      segment ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i) := by
    rw [heq]
    exact right_mem_segment _ _ _
  have hnb : cellFanStart o j w split' n ∈
      segment ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i) := by
    rw [heq]
    exact left_mem_segment _ _ _
  constructor
  · exact tangent_normal_injective i.1
      ((normal_endpoints o ℓ z split i).1.trans
        (normal_mem_segment o ℓ z split i hna).symm) ha
  · exact tangent_normal_injective i.1
      ((normal_endpoints o ℓ z split i).2.trans
        (normal_mem_segment o ℓ z split i hnb).symm) hb

private theorem nontrivial_side_inter_eq (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (s t : Fin 4)
    (h : (dyadicCellSide o ℓ z s ∩ dyadicCellSide o ℓ z t).Nontrivial) : s = t := by
  by_contra hne
  rcases h with ⟨x, hx, y, hy, hxy⟩
  have hx₁ := normal_mem_segment o ℓ z (fun _ ↦ false) ⟨s, 0⟩ hx.1
  have hx₂ := normal_mem_segment o ℓ z (fun _ ↦ false) ⟨t, 0⟩ hx.2
  have hy₁ := normal_mem_segment o ℓ z (fun _ ↦ false) ⟨s, 0⟩ hy.1
  have hy₂ := normal_mem_segment o ℓ z (fun _ ↦ false) ⟨t, 0⟩ hy.2
  have hq : 0 < (2 : ℝ) ^ ℓ / 2 := by positivity
  fin_cases s <;> fin_cases t <;>
    norm_num [normal, normalSign] at hx₁ hx₂ hy₁ hy₂
  all_goals first
    | exact hne rfl
    | exact hxy (Prod.ext (by linarith) (by linarith))

private theorem elementary_subset_closure (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (i : CellFanSlot split) :
    segment ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i) ⊆
      closure (dyadicCell o ℓ z) := by
  intro x hx
  rw [← cellFanPolygons_cover o ℓ z split]
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  have hr := cellFanPolygons_inter_eq o ℓ z split i i
  simp only [Set.inter_self] at hr
  rw [hr]
  exact Or.inr (subset_convexJoin_right (Set.singleton_nonempty _) hx)

private theorem midpoint_halves_inter_subsingleton (a b : ℝ × ℝ) :
    (segment ℝ a (midpoint ℝ a b) ∩ segment ℝ (midpoint ℝ a b) b).Subsingleton := by
  have heq {x : ℝ × ℝ}
      (hx : x ∈ segment ℝ a (midpoint ℝ a b) ∩ segment ℝ (midpoint ℝ a b) b) :
      x = midpoint ℝ a b := by
    have h₁ := dist_add_dist_of_mem_segment hx.1
    have h₂ := dist_add_dist_of_mem_segment hx.2
    have h₃ := dist_add_dist_of_mem_segment (midpoint_mem_segment (𝕜 := ℝ) a b)
    have h₄ := dist_triangle a x b
    have h₅ := dist_nonneg (x := x) (y := midpoint ℝ a b)
    rw [dist_comm (midpoint ℝ a b) x] at h₂
    exact dist_eq_zero.mp (by linarith)
  exact fun x hx y hy ↦ (heq hx).trans (heq hy).symm

private theorem same_split_side_inter_eq (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split split' : Fin 4 → Bool) (i : CellFanSlot split) (n : CellFanSlot split')
    (hside : i.1 = n.1) (hi : split i.1 = true) (hn : split' n.1 = true)
    (h : (segment ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i) ∩
      segment ℝ (cellFanStart o ℓ z split' n) (cellFanEnd o ℓ z split' n)).Nontrivial) :
    segment ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i) =
      segment ℝ (cellFanStart o ℓ z split' n) (cellFanEnd o ℓ z split' n) := by
  rcases cellFan_elementary_endpoints_cases o ℓ z split i with ⟨hm, _, _⟩ |
    ⟨_, ha, hb⟩ | ⟨_, ha, hb⟩
  · simp [hi] at hm
  all_goals rcases cellFan_elementary_endpoints_cases o ℓ z split' n with ⟨hm, _, _⟩ |
    ⟨_, hc, hd⟩ | ⟨_, hc, hd⟩
  all_goals try simp [hn] at hm
  all_goals rw [ha, hb, hc, hd, ← hside] at h ⊢
  all_goals apply False.elim
  all_goals first
    | exact (midpoint_halves_inter_subsingleton
        (cellFanStart o ℓ z (fun _ ↦ false) ⟨i.1, 0⟩)
        (cellFanEnd o ℓ z (fun _ ↦ false) ⟨i.1, 0⟩)).not_nontrivial h
    | exact (midpoint_halves_inter_subsingleton
        (cellFanStart o ℓ z (fun _ ↦ false) ⟨i.1, 0⟩)
        (cellFanEnd o ℓ z (fun _ ↦ false) ⟨i.1, 0⟩)).not_nontrivial
        (by simpa only [Set.inter_comm] using h)

private theorem endpoints_change_mask (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split split' : Fin 4 → Bool) (s : Fin 4) (v : ℕ)
    (hv : v < if split s then 2 else 1) (hv' : v < if split' s then 2 else 1)
    (hs : split s = split' s) :
    cellFanStart o ℓ z split ⟨s, ⟨v, hv⟩⟩ =
        cellFanStart o ℓ z split' ⟨s, ⟨v, hv'⟩⟩ ∧
      cellFanEnd o ℓ z split ⟨s, ⟨v, hv⟩⟩ =
        cellFanEnd o ℓ z split' ⟨s, ⟨v, hv'⟩⟩ := by
  constructor
  · change cellFanCenter o ℓ z + ((2 : ℝ) ^ ℓ / 2) •
      sideVector s (if split s then (v : ℝ) - 1 else -1) =
      cellFanCenter o ℓ z + ((2 : ℝ) ^ ℓ / 2) •
      sideVector s (if split' s then (v : ℝ) - 1 else -1)
    rw [hs]
  · change cellFanCenter o ℓ z + ((2 : ℝ) ^ ℓ / 2) •
      sideVector s (if split s then (v : ℝ) else 1) =
      cellFanCenter o ℓ z + ((2 : ℝ) ^ ℓ / 2) •
      sideVector s (if split' s then (v : ℝ) else 1)
    rw [hs]

private theorem true_slot (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (s : Fin 4) (n : Fin 2) (hs : split s = true) :
    ∃ i : CellFanSlot split, i.1 = s ∧
      cellFanStart o ℓ z split i = cellFanStart o ℓ z (fun _ ↦ true) ⟨s, n⟩ ∧
      cellFanEnd o ℓ z split i = cellFanEnd o ℓ z (fun _ ↦ true) ⟨s, n⟩ := by
  have hn : n.val < if split s then 2 else 1 := by simpa [hs] using n.isLt
  exact ⟨⟨s, ⟨n.val, hn⟩⟩, rfl,
    endpoints_change_mask o ℓ z split (fun _ ↦ true) s n.val hn n.isLt hs⟩

private theorem unsplit_endpoints (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (i : CellFanSlot split) (hi : split i.1 = false) :
    cellFanStart o ℓ z split i = cellFanStart o ℓ z (fun _ ↦ false) ⟨i.1, 0⟩ ∧
      cellFanEnd o ℓ z split i = cellFanEnd o ℓ z (fun _ ↦ false) ⟨i.1, 0⟩ := by
  rcases cellFan_elementary_endpoints_cases o ℓ z split i with ⟨_, ha, hb⟩ |
    ⟨hm, _, _⟩ | ⟨hm, _, _⟩
  · exact ⟨ha, hb⟩
  all_goals simp [hi] at hm

private theorem whole_endpoints_ne (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ) (s : Fin 4) :
    cellFanStart o ℓ z (fun _ ↦ false) ⟨s, 0⟩ ≠
      cellFanEnd o ℓ z (fun _ ↦ false) ⟨s, 0⟩ := by
  intro he
  have ht := tangent_start_lt_end o ℓ z (fun _ ↦ false) ⟨s, 0⟩
  rw [he] at ht
  exact (lt_irrefl _ ht)

private theorem full_midpoint_halves (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ) (s : Fin 4) :
    let a := cellFanStart o ℓ z (fun _ ↦ false) ⟨s, 0⟩
    let b := cellFanEnd o ℓ z (fun _ ↦ false) ⟨s, 0⟩
    (cellFanStart o ℓ z (fun _ ↦ true) ⟨s, 0⟩ = a ∧
      cellFanEnd o ℓ z (fun _ ↦ true) ⟨s, 0⟩ = midpoint ℝ a b) ∧
    (cellFanStart o ℓ z (fun _ ↦ true) ⟨s, 1⟩ = midpoint ℝ a b ∧
      cellFanEnd o ℓ z (fun _ ↦ true) ⟨s, 1⟩ = b) := by
  dsimp only
  have h₀ : cellFanStart o ℓ z (fun _ ↦ true) ⟨s, 0⟩ =
      cellFanStart o ℓ z (fun _ ↦ false) ⟨s, 0⟩ := by
    change cellFanCenter o ℓ z + ((2 : ℝ) ^ ℓ / 2) •
      sideVector s (((0 : Fin 2).val : ℝ) - 1) =
      cellFanCenter o ℓ z + ((2 : ℝ) ^ ℓ / 2) • sideVector s (-1)
    norm_num
  have h₁ : cellFanEnd o ℓ z (fun _ ↦ true) ⟨s, 1⟩ =
      cellFanEnd o ℓ z (fun _ ↦ false) ⟨s, 0⟩ := by
    change cellFanCenter o ℓ z + ((2 : ℝ) ^ ℓ / 2) •
      sideVector s (((1 : Fin 2).val : ℝ)) =
      cellFanCenter o ℓ z + ((2 : ℝ) ^ ℓ / 2) • sideVector s 1
    norm_num
  have hne := whole_endpoints_ne o ℓ z s
  constructor
  · refine ⟨h₀, ?_⟩
    rcases cellFan_elementary_endpoints_cases o ℓ z (fun _ ↦ true) ⟨s, 0⟩ with
      ⟨hm, _, _⟩ | ⟨_, _, hb⟩ | ⟨_, ha, _⟩
    · simp at hm
    · exact hb
    · exact False.elim (hne ((midpoint_eq_left_iff ℝ).mp (ha.symm.trans h₀)))
  · refine ⟨?_, h₁⟩
    rcases cellFan_elementary_endpoints_cases o ℓ z (fun _ ↦ true) ⟨s, 1⟩ with
      ⟨hm, _, _⟩ | ⟨_, _, hb⟩ | ⟨_, ha, _⟩
    · simp at hm
    · exact False.elim (hne ((midpoint_eq_right_iff ℝ).mp (hb.symm.trans h₁)))
    · exact ha

private theorem equal_whole_match (o : ℝ × ℝ) (k₀ k h : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (z w : ℤ × ℤ)
    (i : CellFanSlot (fineLayerSplitMask o k₀ k Z C z)) (t : Fin 4)
    (hop : t = i.1 + 2)
    (heq : dyadicCellSide o (fineScaleIndex k) z i.1 =
      dyadicCellSide o (fineScaleIndex h) w t) :
    ∃ n : CellFanSlot (fineLayerSplitMask o k₀ h Z C w), n.1 = t ∧
      cellFanStart o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i =
        cellFanEnd o (fineScaleIndex h) w (fineLayerSplitMask o k₀ h Z C w) n ∧
      cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i =
        cellFanStart o (fineScaleIndex h) w (fineLayerSplitMask o k₀ h Z C w) n := by
  obtain ⟨ha, hb⟩ := endpoints_reversed o (fineScaleIndex k) (fineScaleIndex h) z w
    (fun _ ↦ false) (fun _ ↦ false) ⟨i.1, 0⟩ ⟨t, 0⟩ hop heq
  have hm : midpoint ℝ
      (cellFanStart o (fineScaleIndex k) z (fun _ ↦ false) ⟨i.1, 0⟩)
      (cellFanEnd o (fineScaleIndex k) z (fun _ ↦ false) ⟨i.1, 0⟩) =
      midpoint ℝ (cellFanStart o (fineScaleIndex h) w (fun _ ↦ false) ⟨t, 0⟩)
        (cellFanEnd o (fineScaleIndex h) w (fun _ ↦ false) ⟨t, 0⟩) := by
    rw [ha, hb, midpoint_comm]
  have hmask : fineLayerSplitMask o k₀ k Z C z i.1 =
      fineLayerSplitMask o k₀ h Z C w t := by
    classical
    unfold fineLayerSplitMask
    apply Bool.decide_congr
    constructor
    · rintro ⟨p, hp, v, hv, ε, hε⟩
      exact ⟨p, hp, v, hv, ε, hε.trans hm⟩
    · rintro ⟨p, hp, v, hv, ε, hε⟩
      exact ⟨p, hp, v, hv, ε, hε.trans hm.symm⟩
  rcases cellFan_elementary_endpoints_cases o (fineScaleIndex k) z
    (fineLayerSplitMask o k₀ k Z C z) i with ⟨hi, hi₁, hi₂⟩ |
      ⟨hi, hi₁, hi₂⟩ | ⟨hi, hi₁, hi₂⟩
  · have ht : fineLayerSplitMask o k₀ h Z C w t = false := hmask.symm.trans hi
    let n : CellFanSlot (fineLayerSplitMask o k₀ h Z C w) :=
      ⟨t, ⟨0, by simp [ht]⟩⟩
    obtain ⟨hn₁, hn₂⟩ := unsplit_endpoints o (fineScaleIndex h) w
      (fineLayerSplitMask o k₀ h Z C w) n ht
    exact ⟨n, rfl, hi₁.trans (ha.trans hn₂.symm), hi₂.trans (hb.trans hn₁.symm)⟩
  · have ht : fineLayerSplitMask o k₀ h Z C w t = true := hmask.symm.trans hi
    obtain ⟨n, hns, hn₁, hn₂⟩ := true_slot o (fineScaleIndex h) w
      (fineLayerSplitMask o k₀ h Z C w) t 1 ht
    have hf := (full_midpoint_halves o (fineScaleIndex h) w t).2
    exact ⟨n, hns, hi₁.trans (ha.trans (hn₂.trans hf.2).symm),
      hi₂.trans (hm.trans (hn₁.trans hf.1).symm)⟩
  · have ht : fineLayerSplitMask o k₀ h Z C w t = true := hmask.symm.trans hi
    obtain ⟨n, hns, hn₁, hn₂⟩ := true_slot o (fineScaleIndex h) w
      (fineLayerSplitMask o k₀ h Z C w) t 0 ht
    have hf := (full_midpoint_halves o (fineScaleIndex h) w t).1
    exact ⟨n, hns, hi₁.trans (hm.trans (hn₂.trans hf.2).symm),
      hi₂.trans (hb.trans (hn₁.trans hf.1).symm)⟩

private theorem half_whole_masks (o : ℝ × ℝ) (k₀ k h : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (z w : ℤ × ℤ) (s t : Fin 4) (n : Fin 2)
    (hC : 2 ≤ C) (hh : 50000000 ≤ h) (hk₀ : k₀ ≤ k)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (hw : w ∈ fineLayerIndices o h (fineScaleIndex h) Z C) (hop : t = s + 2)
    (heq : dyadicCellSide o (fineScaleIndex k) z s = segment ℝ
      (cellFanStart o (fineScaleIndex h) w (fun _ ↦ true) ⟨t, n⟩)
      (cellFanEnd o (fineScaleIndex h) w (fun _ ↦ true) ⟨t, n⟩)) :
    fineLayerSplitMask o k₀ k Z C z s = false ∧
      fineLayerSplitMask o k₀ h Z C w t = true := by
  obtain ⟨ha, hb⟩ := endpoints_reversed o (fineScaleIndex k) (fineScaleIndex h) z w
    (fun _ ↦ false) (fun _ ↦ true) ⟨s, 0⟩ ⟨t, n⟩ hop heq
  obtain ⟨ε, η, hε, hη⟩ := cellFan_unsplit_endpoints_are_corners o (fineScaleIndex k) z s
  have hcorner : ∃ e : Fin 2 × Fin 2,
      dyadicCellCorner o (fineScaleIndex k) z e = midpoint ℝ
        (cellFanStart o (fineScaleIndex h) w (fun _ ↦ false) ⟨t, 0⟩)
        (cellFanEnd o (fineScaleIndex h) w (fun _ ↦ false) ⟨t, 0⟩) := by
    rcases cellFan_elementary_endpoints_cases o (fineScaleIndex h) w
      (fun _ ↦ true) ⟨t, n⟩ with ⟨hm, _, _⟩ | ⟨_, _, hd⟩ | ⟨_, hc, _⟩
    · simp at hm
    · exact ⟨ε, hε.symm.trans (ha.trans hd)⟩
    · exact ⟨η, hη.symm.trans (hb.trans hc)⟩
  obtain ⟨e, he⟩ := hcorner
  have htrue : fineLayerSplitMask o k₀ h Z C w t = true :=
    (fineLayerSplitMask_eq_true_iff o k₀ h Z C w t).mpr ⟨k, hk₀, z, hz, e, he⟩
  obtain ⟨j, hj, hj₁, hj₂⟩ := true_slot o (fineScaleIndex h) w
    (fineLayerSplitMask o k₀ h Z C w) t n htrue
  refine ⟨?_, htrue⟩
  cases hm : fineLayerSplitMask o k₀ k Z C z s
  · rfl
  · obtain ⟨p, hp₀, v, hv, e', he'⟩ :=
      (fineLayerSplitMask_eq_true_iff o k₀ k Z C z s).mp hm
    have hseg : dyadicCellCorner o (fineScaleIndex p) v e' ∈ segment ℝ
        (cellFanStart o (fineScaleIndex h) w (fineLayerSplitMask o k₀ h Z C w) j)
        (cellFanEnd o (fineScaleIndex h) w (fineLayerSplitMask o k₀ h Z C w) j) := by
      rw [hj₁, hj₂, ← heq, he']
      exact midpoint_mem_segment (𝕜 := ℝ) _ _
    have hend := fineLayer_corner_on_elementarySide o k₀ h p Z C w v j e'
      hC hh hw hp₀ hv hseg
    have hne := whole_endpoints_ne o (fineScaleIndex k) z s
    rcases hend with hleft | hright
    · have heq' := he'.symm.trans (hleft.trans (hj₁.trans hb.symm))
      exact False.elim (hne ((midpoint_eq_right_iff ℝ).mp heq'))
    · have heq' := he'.symm.trans (hright.trans (hj₂.trans ha.symm))
      exact False.elim (hne ((midpoint_eq_left_iff ℝ).mp heq'))

private theorem facing_side (o : ℝ × ℝ) (ℓ j : ℕ) (z w : ℤ × ℤ)
    (split : Fin 4 → Bool) (i : CellFanSlot split) (s : Fin 4)
    (hI : closure (dyadicCell o ℓ z) ∩ closure (dyadicCell o j w) ⊆
      dyadicCellSide o ℓ z s)
    (hcontact : (segment ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i) ∩
      closure (dyadicCell o j w)).Nontrivial) : i.1 = s := by
  apply nontrivial_side_inter_eq o ℓ z i.1 s
  apply hcontact.mono
  intro x hx
  exact ⟨cellFan_elementary_segment_subset_whole o ℓ z split i hx.1,
    hI ⟨elementary_subset_closure o ℓ z split i hx.1, hx.2⟩⟩

private theorem opposite_symm {s t : Fin 4} (h : t = s + 2) : s = t + 2 := by
  rw [h]
  fin_cases s <;> decide

/-- Every actual elementary segment with positive-length contact with another
actual fine cell is an elementary segment of that cell with reversed endpoints.
Both cells belong to the family at or above the starting layer; only the
reference layer needs the late-scale bound. Equal-sized split sides match on
each of their two halves. Source: area-law Section 11, lines 299–306. -/
theorem fineLayer_elementary_contact_match (o : ℝ × ℝ) (k₀ k h : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (z w : ℤ × ℤ)
    (hC : 2 ≤ C) (hk : 50000000 ≤ k) (hk₀ : k₀ ≤ k) (hh₀ : k₀ ≤ h)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (hw : w ∈ fineLayerIndices o h (fineScaleIndex h) Z C)
    (hne : (k, z) ≠ (h, w))
    (i : CellFanSlot (fineLayerSplitMask o k₀ k Z C z))
    (hcontact : (segment ℝ
      (cellFanStart o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i)
      (cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i) ∩
      closure (dyadicCell o (fineScaleIndex h) w)).Nontrivial) :
    ∃ j : CellFanSlot (fineLayerSplitMask o k₀ h Z C w), j.1 = i.1 + 2 ∧
      cellFanStart o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i =
        cellFanEnd o (fineScaleIndex h) w (fineLayerSplitMask o k₀ h Z C w) j ∧
      cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i =
        cellFanStart o (fineScaleIndex h) w (fineLayerSplitMask o k₀ h Z C w) j := by
  have hpair : (closure (dyadicCell o (fineScaleIndex k) z) ∩
      closure (dyadicCell o (fineScaleIndex h) w)).Nontrivial := hcontact.mono
    (fun x hx ↦ ⟨elementary_subset_closure o (fineScaleIndex k) z
      (fineLayerSplitMask o k₀ k Z C z) i hx.1, hx.2⟩)
  obtain ⟨s, t, hop, hcases⟩ := fineLayer_closedCell_contact o k h Z C z w
    hC hk hz hw hne hpair
  rcases hcases with ⟨_, hI, hwhole⟩ | ⟨hscale, hI, n, hhalf⟩ |
    ⟨_, hI, n, hhalf⟩
  · have hf := facing_side o (fineScaleIndex k) (fineScaleIndex h) z w
      (fineLayerSplitMask o k₀ k Z C z) i s (fun _ hx ↦ hI ▸ hx) hcontact
    have hop' : t = i.1 + 2 := by simpa only [hf] using hop
    obtain ⟨j, hj, ha, hb⟩ := equal_whole_match o k₀ k h Z C z w i t hop'
      (by simpa only [hf] using hwhole)
    exact ⟨j, hj.trans hop', ha, hb⟩
  · have hf := facing_side o (fineScaleIndex k) (fineScaleIndex h) z w
      (fineLayerSplitMask o k₀ k Z C z) i s (fun _ hx ↦ hI ▸ hx) hcontact
    have hop' : t = i.1 + 2 := by simpa only [hf] using hop
    have hkh : k ≤ h := by
      by_contra! hlt
      have hm := fineScaleIndex_mono hlt.le
      omega
    obtain ⟨hsmall, hbig⟩ := half_whole_masks o k₀ k h Z C z w s t n
      hC (hk.trans hkh) hk₀ hz hw hop hhalf
    obtain ⟨j, hj, hj₁, hj₂⟩ := true_slot o (fineScaleIndex h) w
      (fineLayerSplitMask o k₀ h Z C w) t n hbig
    obtain ⟨hi₁, hi₂⟩ := unsplit_endpoints o (fineScaleIndex k) z
      (fineLayerSplitMask o k₀ k Z C z) i (by simpa only [hf] using hsmall)
    have hseg : segment ℝ
        (cellFanStart o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i)
        (cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i) =
        segment ℝ
          (cellFanStart o (fineScaleIndex h) w (fineLayerSplitMask o k₀ h Z C w) j)
          (cellFanEnd o (fineScaleIndex h) w (fineLayerSplitMask o k₀ h Z C w) j) := by
      rw [hi₁, hi₂, hf, hj₁, hj₂]
      exact hhalf
    exact ⟨j, hj.trans hop', endpoints_reversed o (fineScaleIndex k) (fineScaleIndex h)
      z w (fineLayerSplitMask o k₀ k Z C z) (fineLayerSplitMask o k₀ h Z C w)
      i j (hj.trans hop') hseg⟩
  · have hsub : closure (dyadicCell o (fineScaleIndex k) z) ∩
        closure (dyadicCell o (fineScaleIndex h) w) ⊆
        dyadicCellSide o (fineScaleIndex k) z s := by
      intro x hx
      have hx' : x ∈ dyadicCellSide o (fineScaleIndex h) w t := hI ▸ hx
      rw [hhalf] at hx'
      exact cellFan_elementary_segment_subset_whole o (fineScaleIndex k) z
        (fun _ ↦ true) ⟨s, n⟩ hx'
    have hf := facing_side o (fineScaleIndex k) (fineScaleIndex h) z w
      (fineLayerSplitMask o k₀ k Z C z) i s hsub hcontact
    have hop' : t = i.1 + 2 := by simpa only [hf] using hop
    obtain ⟨hsmall, hbig⟩ := half_whole_masks o k₀ h k Z C w z t s n
      hC hk hh₀ hw hz (opposite_symm hop) hhalf
    have hhalfContact : (segment ℝ
        (cellFanStart o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i)
        (cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i) ∩
        segment ℝ (cellFanStart o (fineScaleIndex k) z (fun _ ↦ true) ⟨s, n⟩)
          (cellFanEnd o (fineScaleIndex k) z (fun _ ↦ true) ⟨s, n⟩)).Nontrivial := by
      apply hcontact.mono
      intro x hx
      have hxpair : x ∈ closure (dyadicCell o (fineScaleIndex k) z) ∩
          closure (dyadicCell o (fineScaleIndex h) w) :=
        ⟨elementary_subset_closure o (fineScaleIndex k) z
          (fineLayerSplitMask o k₀ k Z C z) i hx.1, hx.2⟩
      have hxsmall : x ∈ dyadicCellSide o (fineScaleIndex h) w t := hI ▸ hxpair
      exact ⟨hx.1, hhalf ▸ hxsmall⟩
    have hseg := same_split_side_inter_eq o (fineScaleIndex k) z
      (fineLayerSplitMask o k₀ k Z C z) (fun _ ↦ true) i ⟨s, n⟩ hf
      (by simpa only [hf] using hbig) rfl hhalfContact
    let j : CellFanSlot (fineLayerSplitMask o k₀ h Z C w) :=
      ⟨t, ⟨0, by simp [hsmall]⟩⟩
    obtain ⟨hj₁, hj₂⟩ := unsplit_endpoints o (fineScaleIndex h) w
      (fineLayerSplitMask o k₀ h Z C w) j hsmall
    have hseg' : segment ℝ
        (cellFanStart o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i)
        (cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i) =
        segment ℝ
          (cellFanStart o (fineScaleIndex h) w (fineLayerSplitMask o k₀ h Z C w) j)
          (cellFanEnd o (fineScaleIndex h) w (fineLayerSplitMask o k₀ h Z C w) j) := by
      rw [hj₁, hj₂]
      exact hseg.trans hhalf.symm
    exact ⟨j, hop', endpoints_reversed o (fineScaleIndex k) (fineScaleIndex h)
      z w (fineLayerSplitMask o k₀ k Z C z) (fineLayerSplitMask o k₀ h Z C w)
      i j hop' hseg'⟩

end TNLean.PEPS.AreaLaw.Geometry

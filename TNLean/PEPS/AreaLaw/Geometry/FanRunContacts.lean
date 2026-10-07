/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.FanRuns
import TNLean.PEPS.AreaLaw.Geometry.SideEndpoints
import TNLean.PEPS.AreaLaw.Geometry.SideSubdivisionMask
import TNLean.PEPS.AreaLaw.Geometry.ElementarySideOpponents

/-
Original formalization from the cited manuscript;
no upstream Lean proof text reused.
Manuscript: OpenAI, A two-dimensional area law from a global spectral gap,
September 24, 2026.
Pinned source: adc7f1241b42e322a6451854ab7e4b4c146bf78a
Manuscript path:
preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/10-geometry.tex

Provenance-ID: 8758-tnlean.peps.arealaw.geometry.cell_fan_triangle_contact
Downstream declaration:
TNLean.PEPS.AreaLaw.Geometry.cellFanPolygons_nontrivial_inter_cases
Source labels: prop:two-families
Source: Section 11, lines 308–323.

Provenance-ID: 8758-tnlean.peps.arealaw.geometry.cell_fan_run_contact
Downstream declaration:
TNLean.PEPS.AreaLaw.Geometry.cellFanRunRegions_contact_colors_ne
Source labels: prop:two-families
Source: Section 11, lines 313–323.

OpenAI Codex (GPT-6) assistance was used in this formalization.
-/

/-!
# Contacts between triangles and runs of one cell fan

Two distinct triangles of an actual cell fan have a nontrivial intersection
only when their perimeter segments are consecutive. Their intersection is
then exactly the radial segment from the cell center to their common endpoint.
Consequently, distinct equal-colored run regions have no nontrivial contact.
The statements allow arbitrary origins, integer cell indices, and optional
midpoint subdivisions; they do not require a choice of global colors.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, lines 308–323, `prop:two-families`.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

private theorem midpoint_halves_inter (a b : ℝ × ℝ) (hab : a ≠ b) :
    segment ℝ a (midpoint ℝ a b) ∩ segment ℝ (midpoint ℝ a b) b =
      {midpoint ℝ a b} := by
  let f : ℝ →ᵃ[ℝ] (ℝ × ℝ) := AffineMap.lineMap a b
  have hf : Function.Injective f := AffineMap.lineMap_injective ℝ hab
  have hi : Set.Icc (0 : ℝ) (1 / 2) ∩ Set.Icc (1 / 2) 1 = {(1 / 2 : ℝ)} :=
    Set.Icc_inter_Icc_eq_singleton (by norm_num) (by norm_num)
  have himage := congrArg (fun s : Set ℝ ↦ f '' s) hi
  rw [Set.image_inter hf] at himage
  have hfirst : f '' Set.Icc (0 : ℝ) (1 / 2) = segment ℝ a (midpoint ℝ a b) := by
    rw [← segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2), image_segment]
    simp [f, midpoint, invOf_eq_inv]
  have hlast : f '' Set.Icc (1 / 2 : ℝ) 1 = segment ℝ (midpoint ℝ a b) b := by
    rw [← segment_eq_Icc (by norm_num : (1 / 2 : ℝ) ≤ 1), image_segment]
    simp [f, midpoint, invOf_eq_inv]
  simpa [hfirst, hlast, f, midpoint, invOf_eq_inv] using himage

private theorem whole_start_ne_end (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (s : Fin 4) :
    cellFanStart o ℓ z (fun _ ↦ false) ⟨s, 0⟩ ≠
      cellFanEnd o ℓ z (fun _ ↦ false) ⟨s, 0⟩ := by
  exact (cellFan_elementary_geometry o ℓ z (fun _ ↦ false) ⟨s, 0⟩).1

private theorem whole_common_point (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (s t : Fin 4) (hst : s ≠ t) {x : ℝ × ℝ}
    (hx : x ∈ segment ℝ (cellFanStart o ℓ z (fun _ ↦ false) ⟨s, 0⟩)
      (cellFanEnd o ℓ z (fun _ ↦ false) ⟨s, 0⟩))
    (hy : x ∈ segment ℝ (cellFanStart o ℓ z (fun _ ↦ false) ⟨t, 0⟩)
      (cellFanEnd o ℓ z (fun _ ↦ false) ⟨t, 0⟩)) :
    (t = s + 1 ∧
      cellFanEnd o ℓ z (fun _ ↦ false) ⟨s, 0⟩ =
        cellFanStart o ℓ z (fun _ ↦ false) ⟨t, 0⟩ ∧
      x = cellFanEnd o ℓ z (fun _ ↦ false) ⟨s, 0⟩) ∨
    (s = t + 1 ∧
      cellFanEnd o ℓ z (fun _ ↦ false) ⟨t, 0⟩ =
        cellFanStart o ℓ z (fun _ ↦ false) ⟨s, 0⟩ ∧
      x = cellFanEnd o ℓ z (fun _ ↦ false) ⟨t, 0⟩) := by
  have hsa := congrArg Prod.fst (cellFan_unsplit_endpoints_coordinates o ℓ z s)
  have hsb := congrArg Prod.snd (cellFan_unsplit_endpoints_coordinates o ℓ z s)
  have hta := congrArg Prod.fst (cellFan_unsplit_endpoints_coordinates o ℓ z t)
  have htb := congrArg Prod.snd (cellFan_unsplit_endpoints_coordinates o ℓ z t)
  dsimp only at hsa hsb hta htb
  have hxs := Prod.segment_subset (𝕜 := ℝ) _ _ hx
  have hys := Prod.segment_subset (𝕜 := ℝ) _ _ hy
  have hX : o.1 + (2 : ℝ) ^ ℓ * z.1 < o.1 + 2 ^ ℓ * (z.1 + 1) := by
    have ht : 0 < (2 : ℝ) ^ ℓ := by positivity
    linarith
  have hY : o.2 + (2 : ℝ) ^ ℓ * z.2 < o.2 + 2 ^ ℓ * (z.2 + 1) := by
    have ht : 0 < (2 : ℝ) ^ ℓ := by positivity
    linarith
  fin_cases s <;> fin_cases t <;> norm_num at hst
  all_goals norm_num at hsa hsb hta htb
  all_goals
    simp only [hsa, hsb, hta, htb, Set.mem_prod,
      segment_eq_Icc', Set.mem_Icc, min_self, max_self,
      min_eq_left hX.le, max_eq_right hX.le, min_eq_right hX.le, max_eq_left hX.le,
      min_eq_left hY.le, max_eq_right hY.le, min_eq_right hY.le, max_eq_left hY.le]
      at hxs hys ⊢
  all_goals
    first
    | left; norm_num
      apply Prod.ext <;> dsimp <;> linarith [hxs.1.1, hxs.1.2, hxs.2.1, hxs.2.2,
          hys.1.1, hys.1.2, hys.2.1, hys.2.2]
    | right; norm_num
      apply Prod.ext <;> dsimp <;> linarith [hxs.1.1, hxs.1.2, hxs.2.1, hxs.2.2,
          hys.1.1, hys.1.2, hys.2.1, hys.2.2]
    | exfalso; linarith [hxs.1.1, hxs.1.2, hxs.2.1, hxs.2.2,
        hys.1.1, hys.1.2, hys.2.1, hys.2.2]

private theorem whole_end_of_mem_elementary (o : ℝ × ℝ) (ℓ : ℕ)
    (z : ℤ × ℤ) (split : Fin 4 → Bool) (i : CellFanSlot split)
    (hx : cellFanEnd o ℓ z (fun _ ↦ false) ⟨i.1, 0⟩ ∈
      segment ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i)) :
    cellFanEnd o ℓ z split i = cellFanEnd o ℓ z (fun _ ↦ false) ⟨i.1, 0⟩ := by
  rcases cellFan_elementary_endpoints_cases o ℓ z split i with
    ⟨_, ha, hb⟩ | ⟨_, ha, hm⟩ | ⟨_, hm, hb⟩
  · exact hb
  · rw [ha, hm] at hx
    exact False.elim ((sbtw_midpoint_of_ne ℝ (whole_start_ne_end o ℓ z i.1)).not_swap_right
      (mem_segment_iff_wbtw.mp hx))
  · exact hb

private theorem whole_start_of_mem_elementary (o : ℝ × ℝ) (ℓ : ℕ)
    (z : ℤ × ℤ) (split : Fin 4 → Bool) (i : CellFanSlot split)
    (hx : cellFanStart o ℓ z (fun _ ↦ false) ⟨i.1, 0⟩ ∈
      segment ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i)) :
    cellFanStart o ℓ z split i = cellFanStart o ℓ z (fun _ ↦ false) ⟨i.1, 0⟩ := by
  rcases cellFan_elementary_endpoints_cases o ℓ z split i with
    ⟨_, ha, hb⟩ | ⟨_, ha, hm⟩ | ⟨_, hm, hb⟩
  · exact ha
  · exact ha
  · rw [hm, hb] at hx
    exact False.elim ((sbtw_midpoint_of_ne ℝ (whole_start_ne_end o ℓ z i.1)).not_swap_left
      (mem_segment_iff_wbtw.mp hx))

private theorem distinct_side_inter (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (i j : CellFanSlot split) (hst : i.1 ≠ j.1)
    (hcontact : (segment ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i) ∩
      segment ℝ (cellFanStart o ℓ z split j) (cellFanEnd o ℓ z split j)).Nonempty) :
    (cellFanEnd o ℓ z split i = cellFanStart o ℓ z split j ∧
      segment ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i) ∩
        segment ℝ (cellFanStart o ℓ z split j) (cellFanEnd o ℓ z split j) =
      {cellFanEnd o ℓ z split i}) ∨
    (cellFanEnd o ℓ z split j = cellFanStart o ℓ z split i ∧
      segment ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i) ∩
        segment ℝ (cellFanStart o ℓ z split j) (cellFanEnd o ℓ z split j) =
      {cellFanEnd o ℓ z split j}) := by
  obtain ⟨x, hxi, hxj⟩ := hcontact
  have hwhole (a : CellFanSlot split) := cellFan_elementary_segment_subset_whole o ℓ z split a
  have hpoint := whole_common_point o ℓ z i.1 j.1 hst (hwhole i hxi) (hwhole j hxj)
  have hnotboth (s t : Fin 4) (h : t = s + 1) : s ≠ t + 1 := by
    fin_cases s <;> fin_cases t <;> norm_num at h <;> norm_num
  rcases hpoint with ⟨hnext, he, hx⟩ | ⟨hnext, he, hx⟩
  · have hi := whole_end_of_mem_elementary o ℓ z split i (hx ▸ hxi)
    have hj := whole_start_of_mem_elementary o ℓ z split j ((hx.trans he) ▸ hxj)
    left
    refine ⟨hi.trans (he.trans hj.symm), Set.Subset.antisymm ?_ ?_⟩
    · intro y hy
      rcases whole_common_point o ℓ z i.1 j.1 hst (hwhole i hy.1) (hwhole j hy.2) with
        ⟨_, _, hy'⟩ | ⟨hback, _, _⟩
      · exact (hy'.trans hi.symm : y = _)
      · exact False.elim (hnotboth i.1 j.1 hnext hback)
    · rintro y rfl
      exact ⟨right_mem_segment ℝ _ _, by
        rw [hi, he, ← hj]
        exact left_mem_segment ℝ _ _⟩
  · have hj := whole_end_of_mem_elementary o ℓ z split j (hx ▸ hxj)
    have hi := whole_start_of_mem_elementary o ℓ z split i ((hx.trans he) ▸ hxi)
    right
    refine ⟨hj.trans (he.trans hi.symm), Set.Subset.antisymm ?_ ?_⟩
    · intro y hy
      rcases whole_common_point o ℓ z i.1 j.1 hst (hwhole i hy.1) (hwhole j hy.2) with
        ⟨hback, _, _⟩ | ⟨_, _, hy'⟩
      · exact False.elim (hnotboth j.1 i.1 hnext hback)
      · exact (hy'.trans hj.symm : y = _)
    · rintro y rfl
      exact ⟨by
        rw [hj, he, ← hi]
        exact left_mem_segment ℝ _ _, right_mem_segment ℝ _ _⟩

private theorem first_half_endpoints (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (i : CellFanSlot split)
    (hs : split i.1 = true) (hi : i.2.val = 0) :
    cellFanStart o ℓ z split i = cellFanStart o ℓ z (fun _ ↦ false) ⟨i.1, 0⟩ ∧
      cellFanEnd o ℓ z split i = midpoint ℝ
        (cellFanStart o ℓ z (fun _ ↦ false) ⟨i.1, 0⟩)
        (cellFanEnd o ℓ z (fun _ ↦ false) ⟨i.1, 0⟩) := by
  have ha : cellFanStart o ℓ z split i =
      cellFanStart o ℓ z (fun _ ↦ false) ⟨i.1, 0⟩ := by
    dsimp only [cellFanStart]
    congr 1
    change (if split i.1 then (i.2.val : ℝ) - 1 else -1) = -1
    simp [hs, hi]
  rcases cellFan_elementary_endpoints_cases o ℓ z split i with
    ⟨hf, _, _⟩ | ⟨_, _, hm⟩ | ⟨_, hm, _⟩
  · simp [hs] at hf
  · exact ⟨ha, hm⟩
  · exact False.elim ((sbtw_midpoint_of_ne ℝ (whole_start_ne_end o ℓ z i.1)).ne_left
      (hm.symm.trans ha))

private theorem last_half_endpoints (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (i : CellFanSlot split)
    (hs : split i.1 = true) (hi : i.2.val = 1) :
    cellFanStart o ℓ z split i = midpoint ℝ
        (cellFanStart o ℓ z (fun _ ↦ false) ⟨i.1, 0⟩)
        (cellFanEnd o ℓ z (fun _ ↦ false) ⟨i.1, 0⟩) ∧
      cellFanEnd o ℓ z split i = cellFanEnd o ℓ z (fun _ ↦ false) ⟨i.1, 0⟩ := by
  have hb : cellFanEnd o ℓ z split i =
      cellFanEnd o ℓ z (fun _ ↦ false) ⟨i.1, 0⟩ := by
    dsimp only [cellFanEnd]
    congr 1
    change (if split i.1 then (i.2.val : ℝ) else 1) = 1
    simp [hs, hi]
  rcases cellFan_elementary_endpoints_cases o ℓ z split i with
    ⟨hf, _, _⟩ | ⟨_, _, hm⟩ | ⟨_, hm, _⟩
  · simp [hs] at hf
  · exact False.elim ((sbtw_midpoint_of_ne ℝ (whole_start_ne_end o ℓ z i.1)).ne_right
      (hm.symm.trans hb))
  · exact ⟨hm, hb⟩

private theorem perimeter_inter_cases (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (i j : CellFanSlot split) (hij : i ≠ j)
    (hcontact : (segment ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i) ∩
      segment ℝ (cellFanStart o ℓ z split j) (cellFanEnd o ℓ z split j)).Nonempty) :
    (cellFanEnd o ℓ z split i = cellFanStart o ℓ z split j ∧
      segment ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i) ∩
        segment ℝ (cellFanStart o ℓ z split j) (cellFanEnd o ℓ z split j) =
      {cellFanEnd o ℓ z split i}) ∨
    (cellFanEnd o ℓ z split j = cellFanStart o ℓ z split i ∧
      segment ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i) ∩
        segment ℝ (cellFanStart o ℓ z split j) (cellFanEnd o ℓ z split j) =
      {cellFanEnd o ℓ z split j}) := by
  by_cases hside : i.1 = j.1
  · rcases i with ⟨s, u⟩
    rcases j with ⟨t, v⟩
    dsimp only at hside
    subst t
    have huv : u.val ≠ v.val := by
      intro h
      exact hij (Sigma.ext rfl (heq_of_eq (Fin.ext h)))
    cases hs : split s
    · have hu : u.val < 1 := by simpa [hs] using u.isLt
      have hv : v.val < 1 := by simpa [hs] using v.isLt
      exact False.elim (huv (by omega))
    · have hu : u.val = 0 ∨ u.val = 1 := by
        have hlt : u.val < 2 := by simpa [hs] using u.isLt
        omega
      have hv : v.val = 0 ∨ v.val = 1 := by
        have hlt : v.val < 2 := by simpa [hs] using v.isLt
        omega
      have ordered (u v : Fin (if split s then 2 else 1))
          (hu : u.val = 0) (hv : v.val = 1) :
          cellFanEnd o ℓ z split ⟨s, u⟩ = cellFanStart o ℓ z split ⟨s, v⟩ ∧
          segment ℝ (cellFanStart o ℓ z split ⟨s, u⟩) (cellFanEnd o ℓ z split ⟨s, u⟩) ∩
            segment ℝ (cellFanStart o ℓ z split ⟨s, v⟩)
              (cellFanEnd o ℓ z split ⟨s, v⟩) = {cellFanEnd o ℓ z split ⟨s, u⟩} := by
        obtain ⟨ha, hm⟩ := first_half_endpoints o ℓ z split ⟨s, u⟩ hs hu
        obtain ⟨hm', hb⟩ := last_half_endpoints o ℓ z split ⟨s, v⟩ hs hv
        rw [ha, hm, hm', hb]
        exact ⟨rfl, midpoint_halves_inter _ _ (whole_start_ne_end o ℓ z s)⟩
      rcases hu with hu | hu <;> rcases hv with hv | hv
      · exact False.elim (huv (hu.trans hv.symm))
      · exact Or.inl (ordered u v hu hv)
      · have h := ordered v u hv hu
        exact Or.inr ⟨h.1, by simpa only [Set.inter_comm] using h.2⟩
      · exact False.elim (huv (hu.trans hv.symm))
  · exact distinct_side_inter o ℓ z split i j hside hcontact

/-- Two distinct fan triangles have a nontrivial intersection only along the
radial edge of two consecutive perimeter segments. The common edge is exact.
Source: area-law Section 11, lines 308–323, `prop:two-families`. -/
theorem cellFanPolygons_nontrivial_inter_cases
    (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (i j : CellFanSlot split)
    (hij : i ≠ j)
    (hcontact : ((cellFanPolygon o ℓ z split i).region ∩
      (cellFanPolygon o ℓ z split j).region).Nontrivial) :
    (cellFanEnd o ℓ z split i = cellFanStart o ℓ z split j ∧
      (cellFanPolygon o ℓ z split i).region ∩
        (cellFanPolygon o ℓ z split j).region =
      segment ℝ (cellFanCenter o ℓ z) (cellFanEnd o ℓ z split i)) ∨
    (cellFanEnd o ℓ z split j = cellFanStart o ℓ z split i ∧
      (cellFanPolygon o ℓ z split i).region ∩
        (cellFanPolygon o ℓ z split j).region =
      segment ℝ (cellFanCenter o ℓ z) (cellFanEnd o ℓ z split j)) := by
  have houter : (segment ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i) ∩
      segment ℝ (cellFanStart o ℓ z split j) (cellFanEnd o ℓ z split j)).Nonempty := by
    by_contra h
    have he := Set.not_nonempty_iff_eq_empty.mp h
    rw [cellFanPolygons_inter_eq o ℓ z split i j, he, convexJoin_empty_right,
      Set.union_empty] at hcontact
    exact Set.not_nontrivial_singleton hcontact
  rcases perimeter_inter_cases o ℓ z split i j hij houter with ⟨hadj, hinter⟩ |
    ⟨hadj, hinter⟩
  · left
    refine ⟨hadj, ?_⟩
    rw [cellFanPolygons_inter_eq o ℓ z split i j, hinter, convexJoin_singletons]
    exact Set.union_eq_right.mpr (Set.singleton_subset_iff.mpr (left_mem_segment ℝ _ _))
  · right
    refine ⟨hadj, ?_⟩
    rw [cellFanPolygons_inter_eq o ℓ z split i j, hinter, convexJoin_singletons]
    exact Set.union_eq_right.mpr (Set.singleton_subset_iff.mpr (left_mem_segment ℝ _ _))

/-- Distinct actual run regions with a nontrivial intersection have opposite
colors. No adjacency between their triangles is supplied as a hypothesis.
Source: area-law Section 11, lines 313–323, `prop:two-families`. -/
theorem cellFanRunRegions_contact_colors_ne
    (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ) (split : Fin 4 → Bool)
    (family : CellFanSlot split → Fin 2)
    (R T : CellFanRun o ℓ z split family)
    (hRT : R ≠ T)
    (hcontact : (cellFanRunRegion o ℓ z split family R ∩
      cellFanRunRegion o ℓ z split family T).Nontrivial) :
    ∀ i ∈ R.supp, ∀ j ∈ T.supp, family i ≠ family j := by
  obtain ⟨x, hx, hxc⟩ := hcontact.exists_ne (cellFanCenter o ℓ z)
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx.1
  obtain ⟨hiR, hxi⟩ := Set.mem_iUnion.mp hxi
  obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx.2
  obtain ⟨hjT, hxj⟩ := Set.mem_iUnion.mp hxj
  have hi : (cellFanRunGraph o ℓ z split family).connectedComponentMk i = R :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff R i).mp hiR
  have hj : (cellFanRunGraph o ℓ z split family).connectedComponentMk j = T :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff T j).mp hjT
  have hcomponents : (cellFanRunGraph o ℓ z split family).connectedComponentMk i ≠
      (cellFanRunGraph o ℓ z split family).connectedComponentMk j := by
    rwa [hi, hj]
  have hij : i ≠ j := fun h ↦ hcomponents (h ▸ rfl)
  have hc : cellFanCenter o ℓ z ∈
      (cellFanPolygon o ℓ z split i).region ∩ (cellFanPolygon o ℓ z split j).region := by
    rw [cellFanPolygons_inter_eq]
    exact Or.inl rfl
  have htri : ((cellFanPolygon o ℓ z split i).region ∩
      (cellFanPolygon o ℓ z split j).region).Nontrivial :=
    Set.nontrivial_of_mem_mem_ne ⟨hxi, hxj⟩ hc hxc
  have hadj : cellFanEnd o ℓ z split i = cellFanStart o ℓ z split j ∨
      cellFanEnd o ℓ z split j = cellFanStart o ℓ z split i := by
    rcases cellFanPolygons_nontrivial_inter_cases o ℓ z split i j hij htri with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hcolors := cellFanRun_adjacent_colors_ne o ℓ z split family i j hadj hcomponents
  intro u hu v hv
  have hu' := (SimpleGraph.ConnectedComponent.mem_supp_iff R u).mp hu
  have hv' := (SimpleGraph.ConnectedComponent.mem_supp_iff T v).mp hv
  have hui := cellFanRun_color_eq o ℓ z split family u i (hu'.trans hi.symm)
  have hvj := cellFanRun_color_eq o ℓ z split family v j (hv'.trans hj.symm)
  rwa [hui, hvj]

end TNLean.PEPS.AreaLaw.Geometry

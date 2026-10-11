/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.SideSubdivision
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Normed.Affine.Convex

/-!
# Side subdivisions determined by actual opposing corners

Each side of an actual fine-layer cell is split precisely when its midpoint
is a corner of an actual fine cell at or above the starting layer. Every such
corner on a resulting elementary segment is an endpoint of that segment.
The mask uses all actual fine cells, including the cells outside the belts.

## References

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, lines 299–310.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Manuscript file:
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/`
`build/sections/10-geometry.tex`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/


noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Split a whole side exactly when its midpoint is an actual fine-cell corner
at or above the starting layer. Source: area-law Section 11, lines 299–310. -/
def fineLayerSplitMask (o : ℝ × ℝ) (k₀ k : ℕ) (Z : Finset (ℤ × ℤ))
    (C : ℕ) (z : ℤ × ℤ) : Fin 4 → Bool := by
  classical
  exact fun s ↦ decide (∃ h ≥ k₀,
    ∃ w ∈ fineLayerIndices o h (fineScaleIndex h) Z C,
    ∃ ε : Fin 2 × Fin 2, dyadicCellCorner o (fineScaleIndex h) w ε = midpoint ℝ
      (cellFanStart o (fineScaleIndex k) z (fun _ ↦ false) ⟨s, 0⟩)
      (cellFanEnd o (fineScaleIndex k) z (fun _ ↦ false) ⟨s, 0⟩))

/-- The actual midpoint mask has exactly the prescribed corner witnesses.
Source: area-law Section 11, lines 299–310. -/
theorem fineLayerSplitMask_eq_true_iff (o : ℝ × ℝ) (k₀ k : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (z : ℤ × ℤ) (s : Fin 4) :
    fineLayerSplitMask o k₀ k Z C z s = true ↔
      ∃ h ≥ k₀, ∃ w ∈ fineLayerIndices o h (fineScaleIndex h) Z C,
      ∃ ε : Fin 2 × Fin 2, dyadicCellCorner o (fineScaleIndex h) w ε = midpoint ℝ
        (cellFanStart o (fineScaleIndex k) z (fun _ ↦ false) ⟨s, 0⟩)
        (cellFanEnd o (fineScaleIndex k) z (fun _ ↦ false) ⟨s, 0⟩) := by
  classical
  simp [fineLayerSplitMask]

private theorem side_interpolation (c : ℝ × ℝ) (r : ℝ) (s : Fin 4) (u : ℝ) :
    c + r • cellFanSideVector s u =
    AffineMap.lineMap (c + r • cellFanSideVector s (-1)) (c + r • cellFanSideVector s 1)
      ((u + 1) / 2) := by
  rw [AffineMap.lineMap_apply_module]
  fin_cases s <;> apply Prod.ext <;> simp [cellFanSideVector] <;> ring

/-- The indexed elementary endpoints are the whole-side affine parametrization
at the corresponding subdivision parameters. Source: Section 11,
`prop:two-families`, lines 299–310. -/
theorem cellFan_elementary_endpoints_lineMap (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (i : CellFanSlot split) :
    cellFanStart o ℓ z split i = AffineMap.lineMap
        (cellFanStart o ℓ z (fun _ ↦ false) ⟨i.1, 0⟩)
        (cellFanEnd o ℓ z (fun _ ↦ false) ⟨i.1, 0⟩)
        (if split i.1 then (i.2.val : ℝ) / 2 else 0) ∧
      cellFanEnd o ℓ z split i = AffineMap.lineMap
        (cellFanStart o ℓ z (fun _ ↦ false) ⟨i.1, 0⟩)
        (cellFanEnd o ℓ z (fun _ ↦ false) ⟨i.1, 0⟩)
        (if split i.1 then ((i.2.val : ℝ) + 1) / 2 else 1) := by
  have hs := side_interpolation (cellFanCenter o ℓ z) ((2 : ℝ) ^ ℓ / 2) i.1
    (if split i.1 then (i.2.val : ℝ) - 1 else -1)
  have he := side_interpolation (cellFanCenter o ℓ z) ((2 : ℝ) ^ ℓ / 2) i.1
    (if split i.1 then (i.2.val : ℝ) else 1)
  change cellFanStart o ℓ z split i = AffineMap.lineMap
    (cellFanStart o ℓ z (fun _ ↦ false) ⟨i.1, 0⟩)
    (cellFanEnd o ℓ z (fun _ ↦ false) ⟨i.1, 0⟩)
    (((if split i.1 then (i.2.val : ℝ) - 1 else -1) + 1) / 2) at hs
  change cellFanEnd o ℓ z split i = AffineMap.lineMap
    (cellFanStart o ℓ z (fun _ ↦ false) ⟨i.1, 0⟩)
    (cellFanEnd o ℓ z (fun _ ↦ false) ⟨i.1, 0⟩)
    (((if split i.1 then (i.2.val : ℝ) else 1) + 1) / 2) at he
  constructor
  · convert hs using 2; split_ifs <;> ring
  · convert he using 2; split_ifs <;> ring

/-- Every optional elementary side is the whole side or one of its midpoint halves.
Source: area-law Section 11, lines 299–310. -/
theorem cellFan_elementary_endpoints_cases (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (i : CellFanSlot split) :
    let a := cellFanStart o ℓ z (fun _ ↦ false) ⟨i.1, 0⟩
    let b := cellFanEnd o ℓ z (fun _ ↦ false) ⟨i.1, 0⟩
    (split i.1 = false ∧ cellFanStart o ℓ z split i = a ∧
      cellFanEnd o ℓ z split i = b) ∨
    (split i.1 = true ∧ cellFanStart o ℓ z split i = a ∧
      cellFanEnd o ℓ z split i = midpoint ℝ a b) ∨
    (split i.1 = true ∧ cellFanStart o ℓ z split i = midpoint ℝ a b ∧
      cellFanEnd o ℓ z split i = b) := by
  dsimp only
  obtain ⟨hs, he⟩ := cellFan_elementary_endpoints_lineMap o ℓ z split i
  cases hm : split i.1
  · exact Or.inl ⟨rfl, by simpa [hm] using hs, by simpa [hm] using he⟩
  · have hj : i.2.val = 0 ∨ i.2.val = 1 := by
      have hlt := i.2.isLt
      simp [hm] at hlt
      omega
    rcases hj with hj | hj
    · exact Or.inr (Or.inl ⟨rfl, by simpa [hm, hj] using hs,
        by simpa [hm, hj, midpoint, invOf_eq_inv] using he⟩)
    · exact Or.inr (Or.inr ⟨rfl, by simpa [hm, hj, midpoint, invOf_eq_inv] using hs,
        by simpa [hm, hj] using he⟩)

/-- An elementary segment lies on its whole cell side for every optional midpoint mask.
Source: area-law Section 11, lines 299–310. -/
theorem cellFan_elementary_segment_subset_whole (o : ℝ × ℝ) (ℓ : ℕ)
    (z : ℤ × ℤ) (split : Fin 4 → Bool) (i : CellFanSlot split) :
    segment ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i) ⊆
      segment ℝ (cellFanStart o ℓ z (fun _ ↦ false) ⟨i.1, 0⟩)
        (cellFanEnd o ℓ z (fun _ ↦ false) ⟨i.1, 0⟩) := by
  rcases cellFan_elementary_endpoints_cases o ℓ z split i with ⟨_, ha, hb⟩ |
    ⟨_, ha, hm⟩ | ⟨_, hm, hb⟩
  · rw [ha, hb]
  · rw [ha, hm]
    exact (convex_segment (𝕜 := ℝ) _ _).segment_subset (left_mem_segment _ _ _)
      (midpoint_mem_segment (𝕜 := ℝ) _ _)
  · rw [hm, hb]
    exact (convex_segment (𝕜 := ℝ) _ _).segment_subset (midpoint_mem_segment (𝕜 := ℝ) _ _)
      (right_mem_segment _ _ _)

/-- The two halves of a segment meet exactly at its midpoint. -/
theorem segment_midpoint_inter_segment {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (a b : E) :
    segment ℝ a (midpoint ℝ a b) ∩ segment ℝ (midpoint ℝ a b) b = {midpoint ℝ a b} := by
  refine Set.eq_singleton_iff_unique_mem.mpr
    ⟨⟨right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩, fun x hx ↦ ?_⟩
  have h₁ := dist_add_dist_of_mem_segment hx.1
  have h₂ := dist_add_dist_of_mem_segment hx.2
  have h₃ := dist_add_dist_of_mem_segment (midpoint_mem_segment (𝕜 := ℝ) a b)
  have h₄ := dist_triangle a x b
  have h₅ := dist_nonneg (x := x) (y := midpoint ℝ a b)
  rw [dist_comm (midpoint ℝ a b) x] at h₂
  exact dist_eq_zero.mp (by linarith)

private theorem trichotomy_on_first_half {a b x : ℝ × ℝ}
    (hthree : x = a ∨ x = midpoint ℝ a b ∨ x = b)
    (hx : x ∈ segment ℝ a (midpoint ℝ a b)) : x = a ∨ x = midpoint ℝ a b := by
  by_cases hab : a = b
  · simpa [hab] using hthree
  rcases hthree with ha | hm | hb
  · exact Or.inl ha
  · exact Or.inr hm
  · exact False.elim ((sbtw_midpoint_of_ne ℝ hab).not_swap_right
      (mem_segment_iff_wbtw.mp (hb ▸ hx)))

private theorem trichotomy_on_last_half {a b x : ℝ × ℝ}
    (hthree : x = a ∨ x = midpoint ℝ a b ∨ x = b)
    (hx : x ∈ segment ℝ (midpoint ℝ a b) b) : x = midpoint ℝ a b ∨ x = b := by
  have hthree' : x = b ∨ x = midpoint ℝ b a ∨ x = a := by
    rcases hthree with ha | hm | hb
    · exact Or.inr (Or.inr ha)
    · exact Or.inr (Or.inl (by simpa only [midpoint_comm] using hm))
    · exact Or.inl hb
  have hx' : x ∈ segment ℝ b (midpoint ℝ b a) := by
    simpa only [segment_symm, midpoint_comm] using hx
  simpa only [midpoint_comm] using (trichotomy_on_first_half hthree' hx').symm

/-- Every actual opposing fine-cell corner on a segment of the actual midpoint
subdivision is one of that segment's endpoints.
Source: area-law Section 11, lines 299–310. -/
theorem fineLayer_corner_on_elementarySide (o : ℝ × ℝ) (k₀ k h : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (z w : ℤ × ℤ)
    (i : CellFanSlot (fineLayerSplitMask o k₀ k Z C z)) (ε : Fin 2 × Fin 2)
    (hC : 2 ≤ C) (hk : 50000000 ≤ k)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C) (hh : k₀ ≤ h)
    (hw : w ∈ fineLayerIndices o h (fineScaleIndex h) Z C)
    (hside : dyadicCellCorner o (fineScaleIndex h) w ε ∈ segment ℝ
      (cellFanStart o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i)
      (cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i)) :
    dyadicCellCorner o (fineScaleIndex h) w ε =
        cellFanStart o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i ∨
      dyadicCellCorner o (fineScaleIndex h) w ε =
        cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i := by
  have hwhole := cellFan_elementary_segment_subset_whole o (fineScaleIndex k) z
    (fineLayerSplitMask o k₀ k Z C z) i hside
  have hthree := fineLayer_corner_on_side o k h Z C z w i.1 ε hC hk hz hw hwhole
  rcases cellFan_elementary_endpoints_cases o (fineScaleIndex k) z
    (fineLayerSplitMask o k₀ k Z C z) i with ⟨hmask, ha, hb⟩ |
      ⟨_, ha, hm⟩ | ⟨_, hm, hb⟩
  · rw [ha, hb]
    rcases hthree with hx | hx | hx
    · exact Or.inl hx
    · have ht := (fineLayerSplitMask_eq_true_iff o k₀ k Z C z i.1).mpr
        ⟨h, hh, w, hw, ε, hx⟩
      simp [hmask] at ht
    · exact Or.inr hx
  · rw [ha, hm] at hside ⊢
    exact trichotomy_on_first_half hthree hside
  · rw [hm, hb] at hside ⊢
    exact trichotomy_on_last_half hthree hside

end TNLean.PEPS.AreaLaw.Geometry

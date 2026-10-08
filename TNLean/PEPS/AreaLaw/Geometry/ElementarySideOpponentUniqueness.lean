/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.ElementarySideOpponents
import Mathlib.Order.Interval.Set.Disjoint

/-!
# Uniqueness of the region opposing an elementary side

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

namespace TNLean.PEPS.AreaLaw.Geometry

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

private def rectangleCorner (a b : ℝ × ℝ) (ε : Fin 2 × Fin 2) : ℝ × ℝ :=
  (if ε.1.val = 0 then a.1 else b.1, if ε.2.val = 0 then a.2 else b.2)

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
    by_contra! hy
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

private theorem midpoint_coordinates (u v : ℝ × ℝ) :
    midpoint ℝ u v = ((u.1 + v.1) / 2, (u.2 + v.2) / 2) := by
  apply Prod.ext <;> norm_num [midpoint_eq_smul_add, smul_eq_mul] <;> ring

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
  rw [midpoint_coordinates, hm] at hx hcorners
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
  let lower (r : ℕ) (v : ℤ × ℤ) := dyadicCellCorner o r v (0, 0)
  let upper (r : ℕ) (v : ℤ × ℤ) := dyadicCellCorner o r v (1, 1)
  have bounds (r : ℕ) (v : ℤ × ℤ) :
      (lower r v).1 < (upper r v).1 ∧ (lower r v).2 < (upper r v).2 := by
    have ht : 0 < (2 : ℝ) ^ r := by positivity
    constructor <;> norm_num [lower, upper, dyadicCellCorner]
  have interior_box (r : ℕ) (v : ℤ × ℤ) : interior (dyadicCell o r v) =
      Set.Ioo (lower r v).1 (upper r v).1 ×ˢ Set.Ioo (lower r v).2 (upper r v).2 := by
    simp [lower, upper, dyadicCellCorner, dyadicCell, interior_prod_eq, interior_Ico]
  have closed_box (r : ℕ) (v : ℤ × ℤ) : closure (dyadicCell o r v) =
      Set.Icc (lower r v).1 (upper r v).1 ×ˢ Set.Icc (lower r v).2 (upper r v).2 := by
    simp [lower, upper, dyadicCellCorner, closure_dyadicCell]
  have hnotcorner (ε : Fin 2 × Fin 2) : dyadicCellCorner o n t ε ≠
      midpoint ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i) := by
    intro he
    have hm := midpoint_mem_segment (𝕜 := ℝ) (cellFanStart o ℓ z split i)
      (cellFanEnd o ℓ z split i)
    rcases hcorners ε (he.symm ▸ hm) with h | h
    · exact hne ((midpoint_eq_left_iff ℝ).mp (he.symm.trans h))
    · exact hne ((midpoint_eq_right_iff ℝ).mp (he.symm.trans h))
  have hcorners' (ε : Fin 2 × Fin 2) : rectangleCorner (lower n t) (upper n t) ε ≠
      midpoint ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i) := by
    intro he
    apply hnotcorner ε
    have hec : rectangleCorner (lower n t) (upper n t) ε = dyadicCellCorner o n t ε := by
      rcases ε with ⟨e, f⟩
      fin_cases e <;> fin_cases f <;> norm_num [rectangleCorner, lower, upper, dyadicCellCorner]
    exact hec.symm.trans he
  have disjoint_box (r s : ℕ) (v u : ℤ × ℤ)
      (hd : Disjoint (dyadicCell o r v) (dyadicCell o s u)) :
      Disjoint (Set.Ioo (lower r v).1 (upper r v).1 ×ˢ
        Set.Ioo (lower r v).2 (upper r v).2)
        (Set.Ioo (lower s u).1 (upper s u).1 ×ˢ
          Set.Ioo (lower s u).2 (upper s u).2) := by
    rw [← interior_box, ← interior_box]
    exact hd.mono interior_subset interior_subset
  obtain ⟨ha, hb⟩ := (cellFan_vertices_mem_beltCellMarks o ℓ z split).2 i
  have haR := beltCellMarks_subset_closure_dyadicCell o ℓ z ha
  have hbR := beltCellMarks_subset_closure_dyadicCell o ℓ z hb
  have haW := hside (left_mem_segment ℝ _ _)
  have hbW := hside (right_mem_segment ℝ _ _)
  rw [closed_box] at haR hbR haW hbW hx
  exact rectangle_axis_no_three (bounds ℓ z) (bounds j w) (bounds n t)
    haR hbR haW hbW hx hne (haxis.imp And.left And.left) hcorners'
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

end TNLean.PEPS.AreaLaw.Geometry

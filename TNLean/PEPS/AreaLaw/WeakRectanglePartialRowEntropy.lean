/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.BufferedRectangles
import TNLean.PEPS.AreaLaw.Geometry.TemplateEntropy

/-!
# Entropy cost of part of a rectangle dilation layer

Adding an arbitrary subset of the next dilation layer changes the regional
entropy by at most twelve times the rectangle size times the logarithm of
the local dimension. The estimate follows from the layer cardinality bound,
the disjoint-region entropy increment inequality, and the dimension bound.
It includes thin rectangles, negative coordinates, an empty added region,
and missing lattice sites in the physical domain.

Source: OpenAI, A two-dimensional area law from a global spectral gap,
September 24, 2026, Lemma 9.4, 08-scanner.tex, lines 666–667, and the
rectangle covering argument for Proposition 9.5, lines 717–729,
at openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
This is the partial-layer auxiliary estimate.
Original formalization from the manuscript; no upstream Lean proof text reused.
-/

namespace TNLean.PEPS.AreaLaw

/-- An arbitrary part of a rectangle dilation layer has entropy cost at most
`12 * size Q * log q`. Source: `08-scanner.tex`, lines 666–667 and 717–729.
The estimate uses only normalization, the local dimension and the layer count. -/
theorem IntRect.partial_row_entropy_le
    (Λ : Finset (ℤ × ℤ)) (q : ℕ) (hq : 1 ≤ q)
    (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1) (A : Finset (Site Λ))
    (Q : IntRect) (j : ℕ) (hj : 1 ≤ j) (hjs : j ≤ Q.size)
    (Y : Finset (ℤ × ℤ))
    (hY : Y ⊆ (Q.dilate j).toFinset \ (Q.dilate (j - 1)).toFinset) :
    |regionalEntropy Λ q Ω
        (A.filter fun x ↦ x.1 ∈ ((Q.dilate (j - 1)).toFinset \ Q.toFinset) ∪ Y) -
      regionalEntropy Λ q Ω
        (A.filter fun x ↦ x.1 ∈ (Q.dilate (j - 1)).toFinset \ Q.toFinset)| ≤
      12 * (Q.size : ℝ) * Real.log q := by
  have hlayer := card_dilate_sdiff_le Q (d := j) (k := 1) hj
  have hcardLayer :
      ((Q.dilate j).toFinset \ (Q.dilate (j - 1)).toFinset).card ≤
        12 * Q.size := by
    omega
  classical
  let R := A.filter fun x ↦ x.1 ∈ (Q.dilate (j - 1)).toFinset \ Q.toFinset
  let B := A.filter fun x ↦ x.1 ∈ Y
  have hd : Disjoint R B := by
    apply Finset.disjoint_left.mpr
    intro x hx hb
    have hx' := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx).2).1
    exact (Finset.mem_sdiff.mp (hY (Finset.mem_filter.mp hb).2)).2 hx'
  have he : (A.filter fun x ↦
      x.1 ∈ ((Q.dilate (j - 1)).toFinset \ Q.toFinset) ∪ Y) = R ∪ B := by
    simp only [R, B, Finset.mem_union, Finset.filter_or]
  have hBY : B.image Subtype.val ⊆ Y := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hz).2
  have hcard : B.card ≤ 12 * Q.size := by
    calc
      B.card = (B.image Subtype.val).card :=
        (Finset.card_image_of_injective B Subtype.val_injective).symm
      _ ≤ Y.card := Finset.card_le_card hBY
      _ ≤ ((Q.dilate j).toFinset \ (Q.dilate (j - 1)).toFinset).card :=
        Finset.card_le_card hY
      _ ≤ 12 * Q.size := hcardLayer
  rw [he]
  calc
    |regionalEntropy Λ q Ω (R ∪ B) - regionalEntropy Λ q Ω R| ≤
        regionalEntropy Λ q Ω B :=
      abs_regionalEntropy_union_sub_le Λ q Ω hΩ R B hd
    _ ≤ (B.card : ℝ) * Real.log q :=
      regionalEntropy_le_card_mul_log Λ q Ω hΩ B
    _ ≤ 12 * (Q.size : ℝ) * Real.log q :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
        (Real.log_nonneg (by exact_mod_cast hq))

end TNLean.PEPS.AreaLaw

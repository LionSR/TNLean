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
entropy by at most `12 * Q.size * Real.log q`, where `q` is the local
dimension. The estimate follows from the layer cardinality bound,
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
  have hXY : Disjoint ((Q.dilate (j - 1)).toFinset \ Q.toFinset) Y :=
    Finset.disjoint_left.mpr fun x hx hy ↦
      (Finset.mem_sdiff.mp (hY hy)).2 (Finset.mem_sdiff.mp hx).1
  refine (abs_regionalEntropy_filter_union_sub_le Λ q hq Ω hΩ A _ Y hXY).trans ?_
  have hcard := (Finset.card_le_card hY).trans hcardLayer
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
    (Real.log_nonneg (by exact_mod_cast hq))

end TNLean.PEPS.AreaLaw

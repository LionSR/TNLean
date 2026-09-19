/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusEdgeBlockingCrossing

/-!
# One-orientation window injectivity and the staircase end pair on the torus

The two-dimensional strengthening of the normal PEPS Fundamental Theorem
(arXiv:1804.04964, the corollary at lines 2297--2318 of
`Papers/1804.04964/paper_normal.tex`) assumes injectivity of a single rectangle
shape: every contiguous `L × K` region of the torus, one orientation only, with
the sizes `n ≥ 2L + 1` and `m ≥ 2K + 1`.  This file is the geometry layer of
that horizontal-window route, scoped in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`;
the complementary vertical route now uses the faithful reference-blocking
theorem `TNLean.PEPS.isCrossingEdge_torusVerticalRectangleBlockingDatum` from
`TNLean.PEPS.TorusRectangleReferenceData`:

* a larger rectangle exhibited as a sliding union of contiguous `L × K`
  windows (`contiguousRectangle_eq_biUnion_window`);
* the staircase end pair of the overlapping-window chain around a horizontal
  edge: two diagonally offset `L × K` windows whose only joining lattice edge
  is the distinguished edge itself (`isCrossingEdge_horizontalStaircase`).

This file is intentionally horizontal-only; the vertical comparison now goes
through the reference-blocking route cited above.

The single-crossing geometry of the end pair is the reason the bond operator
extracted by the window chain lives on one edge; it is consumed by the same
single-boundary-edge comparison machinery as the landed three-block route.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964, the
  corollary and proof sketch at lines 2296--2445 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

namespace TNLean
namespace PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]

/-! ### Sliding-window tiling injectivity -/

/-- A contiguous torus rectangle of width at least `L` and height at least `K`
is the union of the contiguous `L × K` windows sliding over it.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1322--1430
of `Papers/1804.04964/paper_normal.tex`. -/
theorem contiguousRectangle_eq_biUnion_window {L K : ℕ} (hL : 0 < L) (hK : 0 < K)
    (xStart yStart xLen yLen : ℕ) (hx : L ≤ xLen) (hy : K ≤ yLen) :
    (torusContiguousRectangle xStart yStart xLen yLen :
        Finset (TorusVertex width height)) =
      (Finset.range (xLen - L + 1) ×ˢ Finset.range (yLen - K + 1)).biUnion
        (fun p => torusContiguousRectangle (xStart + p.1) (yStart + p.2) L K) := by
  ext v
  simp only [mem_torusContiguousRectangle, Finset.mem_biUnion, Finset.mem_product,
    Finset.mem_range]
  constructor
  · rintro ⟨hx0, hx1, hy0, hy1⟩
    refine ⟨(min (v.1.val - xStart) (xLen - L), min (v.2.val - yStart) (yLen - K)),
      ⟨?_, ?_⟩, ?_⟩
    · omega
    · omega
    · omega
  · rintro ⟨⟨p, q⟩, ⟨_, _⟩, hv⟩
    omega

/-! ### The staircase end pair around a horizontal edge

The overlapping-window chain around a horizontal edge ends on two diagonally
offset `L × K` windows: the left window `[a, a + L) × [b, b + K)`, containing
the left endpoint of the edge at its top-right corner, and the right window
`[a + L, a + 2L) × [b + K - 1, b + 2K - 1)`, containing the right endpoint at
its bottom-left corner.  Their column ranges are disjoint and their row ranges
meet exactly in the row `b + K - 1`, so the only lattice edge joining them is
the distinguished edge. -/

variable [Fact (1 < width)] [Fact (1 < height)]

/-- The four endpoint coordinate values of the distinguished edge of the
horizontal staircase pair: the right edge at `(a + L - 1, b + K - 1)`, when
the coordinates avoid wraparound. -/
theorem horizontalStaircaseEdge_val {L K a b : ℕ} (hL : 0 < L)
    (hxw : a + L < width) (hyh : b + K - 1 < height) :
    (torusRightEdge (((a + L - 1 : ℕ) : ZMod width), ((b + K - 1 : ℕ) : ZMod height)) :
        Edge (torusGraph width height)).1.1.1.val = a + L - 1 ∧
      (torusRightEdge (((a + L - 1 : ℕ) : ZMod width),
        ((b + K - 1 : ℕ) : ZMod height)) :
          Edge (torusGraph width height)).1.1.2.val = b + K - 1 ∧
      (torusRightEdge (((a + L - 1 : ℕ) : ZMod width),
        ((b + K - 1 : ℕ) : ZMod height)) :
          Edge (torusGraph width height)).1.2.1.val = a + L ∧
      (torusRightEdge (((a + L - 1 : ℕ) : ZMod width),
        ((b + K - 1 : ℕ) : ZMod height)) :
          Edge (torusGraph width height)).1.2.2.val = b + K - 1 := by
  have href := torusRightEdge_endpoints_of_lt
    (p := (((a + L - 1 : ℕ) : ZMod width), ((b + K - 1 : ℕ) : ZMod height)))
    (width := width) (height := height)
    (by rw [ZMod.val_cast_of_lt (by omega)]; omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [href.1]; exact ZMod.val_cast_of_lt (by omega)
  · rw [href.1]; exact ZMod.val_cast_of_lt (by omega)
  · rw [href.2]
    change (((a + L - 1 : ℕ) : ZMod width) + 1).val = a + L
    rw [show ((a + L - 1 : ℕ) : ZMod width) + 1 = ((a + L : ℕ) : ZMod width) from by
      rw [← Nat.cast_add_one]; congr 1; omega]
    exact ZMod.val_cast_of_lt (by omega)
  · rw [href.2]; exact ZMod.val_cast_of_lt (by omega)

/-- **The single crossing of the horizontal staircase pair.**

The two diagonally offset `L × K` windows around a horizontal edge --- the left
window `[a, a + L) × [b, b + K)` and the right window
`[a + L, a + 2L) × [b + K - 1, b + 2K - 1)` --- are joined by exactly one
lattice edge, the right edge at `(a + L - 1, b + K - 1)`: a horizontal step
between them forces the columns `a + L - 1`, `a + L` and the single common row
`b + K - 1`, a vertical step is impossible since the column ranges are
disjoint, and a step wrapping the seam lands in the zero column, left of both
windows since `1 ≤ a`.  This single-crossing geometry is what makes the bond
operator extracted by the overlapping-window chain live on the one
distinguished edge.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex` (the comparison of the first and the last
window); scoped in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`. -/
theorem isCrossingEdge_horizontalStaircase {d : ℕ}
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (g : Edge (torusGraph width height)) :
    IsCrossingEdge (G := torusGraph width height) A
        (torusContiguousRectangle a b L K)
        (torusContiguousRectangle (a + L) (b + K - 1) L K) g ↔
      g = torusRightEdge (((a + L - 1 : ℕ) : ZMod width),
        ((b + K - 1 : ℕ) : ZMod height)) := by
  constructor
  · rintro ⟨hRed, hBlue⟩
    simp only [IsRegionBoundaryEdge, mem_torusContiguousRectangle] at hRed hBlue
    -- The ordered-endpoint convention `g.1.1 < g.1.2` in coordinate-value form.
    have hlt := torusEdge_val_lt g
    -- Pin the four coordinate values of `g` to the distinguished edge's coordinates.
    have hcoord : g.1.1.1.val = a + L - 1 ∧ g.1.1.2.val = b + K - 1 ∧
        g.1.2.1.val = a + L ∧ g.1.2.2.val = b + K - 1 := by
      rcases torusEdge_val_cases g with ⟨hpar, hstep⟩ | ⟨hpar, hstep⟩ <;>
        crossing_blocks hRed hBlue
    obtain ⟨hc1, hc2, hc3, hc4⟩ := hcoord
    obtain ⟨hr11, hr12, hr21, hr22⟩ := horizontalStaircaseEdge_val
      (width := width) (height := height) (L := L) (K := K) (a := a) (b := b)
      hL (by omega) (by omega)
    apply Subtype.ext
    refine Prod.ext (torusVertex_eq_of_val_eq ?_ ?_) (torusVertex_eq_of_val_eq ?_ ?_)
    · rw [hc1, hr11]
    · rw [hc2, hr12]
    · rw [hc3, hr21]
    · rw [hc4, hr22]
  · rintro rfl
    obtain ⟨hr11, hr12, hr21, hr22⟩ := horizontalStaircaseEdge_val
      (width := width) (height := height) (L := L) (K := K) (a := a) (b := b)
      hL (by omega) (by omega)
    refine ⟨Or.inl ⟨?_, ?_⟩, Or.inr ⟨?_, ?_⟩⟩
    · rw [mem_torusContiguousRectangle]; omega
    · rw [mem_torusContiguousRectangle]; omega
    · rw [mem_torusContiguousRectangle]; omega
    · rw [mem_torusContiguousRectangle]; omega

end PEPS
end TNLean

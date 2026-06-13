import TNLean.PEPS.TorusWindowChain6

/-!
# The single-crossing geometry of the staircase end pair

The two-dimensional strengthening of the normal PEPS Fundamental Theorem
(arXiv:1804.04964, the corollary at lines 2297--2318 of
`Papers/1804.04964/paper_normal.tex`) closes its proof sketch with the single-crossing
extraction (Step 4): the two end windows of the overlapping-window chain around a horizontal
edge are diagonally offset `L × K` rectangles whose column ranges are disjoint and whose row
ranges meet only at one row, so the *only* lattice edge joining them is the distinguished edge
`e`.  The open-boundary end-pair equality `staircasePair_insert_eq_open` of
`TNLean/PEPS/TorusWindowChain6.lean` is therefore a pairing of two injective tensors across the
single bond `e`, the geometry that makes the extracted bond operator live on one edge.

This file lifts the single-crossing characterization `isCrossingEdge_horizontalStaircase` of
`TNLean/PEPS/TorusWindowRegion.lean` from the abstract coordinate rectangles to the actual end
windows of the staircase family — `horizontalStaircaseLeftWindow` (the last window
`W_{L+K-1}`) and `horizontalStaircaseRightWindow` (the first window `W_0`) — and records the
two boundary facts the extraction rests on:

* the distinguished edge `e = horizontalStaircaseReferenceEdge` is the unique crossing edge
  between the two end windows (`isCrossingEdge_horizontalStaircaseEndWindows`), hence a boundary
  edge of each (`isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge`,
  `isRegionBoundaryEdge_horizontalStaircaseRightWindow_referenceEdge`);
* `e` is *not* a boundary edge of the end pair `S = W_0 ⊔ W_{L+K-1}`
  (`not_isRegionBoundaryEdge_horizontalStaircaseEndPair_referenceEdge`): both its endpoints lie
  in `S`, one in each window, so `e` is the single interior bond of `S` summed over when the
  two windows are contracted together.

The single crossing means that in the end-pair contraction the bond `e` is the only virtual
leg shared by the two windows; every other open leg of each window crosses the boundary of `S`.
This is the geometric content of the source's "the comparison of the first and the last window"
and the reason the matrix extracted by the standard two-sided argument lives on the one bond
`e` (arXiv:1804.04964, the matrix-level extraction
`MPSChainTensor.exists_bondOperator_of_intertwine_span` after `eq:inj_O->X_argument`, line 377
of `Papers/1804.04964/paper_normal.tex`).

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, the corollary and proof sketch at lines
  2296--2445 of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964); the
  filled-in derivation in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 4.
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

section Torus

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (1 < width)] [Fact (1 < height)]
variable {d : ℕ}

/-! ### The distinguished edge of the staircase end pair

The reference edge of the horizontal staircase is the right edge at the top-right corner of the
left end window, equivalently the bottom-left corner of the right end window: the unique lattice
edge joining the two end windows. -/

/-- The distinguished edge `e` of the horizontal staircase end pair around the staircase corner
`s = (a, b)`: the right edge at `(a + L - 1, b + K - 1)`, joining the left end window
`[a, a + L) × [b, b + K)` to the right end window `[a + L, a + 2L) × [b + K - 1, b + 2K - 1)`.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex` (the highlighted edge of the window chain);
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 4. -/
def horizontalStaircaseReferenceEdge (s : TorusVertex width height) (L K : ℕ) :
    Edge (torusGraph width height) :=
  torusRightEdge ((s.1 + ((L - 1 : ℕ) : ZMod width)), (s.2 + ((K - 1 : ℕ) : ZMod height)))

/-! ### The single crossing of the end windows

The left and right end windows are the coordinate rectangles of
`isCrossingEdge_horizontalStaircase` once the staircase corner is read with natural-number
coordinates and the no-wraparound bounds hold.  The lift identifies the two `torusArcRectangle`
windows with the lemma's `torusContiguousRectangle` rectangles and the reference edge with the
lemma's distinguished edge. -/

/-- **The single crossing of the staircase end windows.**

For a staircase corner `s = ((a : ZMod width), (b : ZMod height))` with `1 ≤ a` and the
no-wraparound bounds `a + 2 * L ≤ width`, `b + 2 * K - 1 ≤ height`, the only lattice edge
joining the left end window `horizontalStaircaseLeftWindow` and the right end window
`horizontalStaircaseRightWindow` is the reference edge `horizontalStaircaseReferenceEdge`.  This
is `isCrossingEdge_horizontalStaircase` of `TNLean/PEPS/TorusWindowRegion.lean` read on the
actual end windows: the two `torusArcRectangle` windows are the lemma's coordinate rectangles
(`torusArcRectangle_eq_torusContiguousRectangle`), and the reference edge is the lemma's
distinguished edge.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex` (the comparison of the first and the last window);
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 4. -/
theorem isCrossingEdge_horizontalStaircaseEndWindows
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (g : Edge (torusGraph width height)) :
    IsCrossingEdge (G := torusGraph width height) A
        (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
        (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K) g ↔
      g = horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K := by
  -- Identify the two end windows with the lemma's coordinate rectangles.
  have hleft : horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K =
      torusContiguousRectangle a b L K := by
    rw [horizontalStaircaseLeftWindow,
      torusArcRectangle_eq_torusContiguousRectangle a b L K hL hK (by omega) (by omega)]
  have hright : horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K =
      torusContiguousRectangle (a + L) (b + K - 1) L K := by
    rw [horizontalStaircaseRightWindow]
    -- The right window start is the cast of the natural-number coordinates `(a + L, b + K - 1)`.
    have hx : ((a : ZMod width) + (L : ZMod width)) = ((a + L : ℕ) : ZMod width) := by
      push_cast; ring
    have hy : ((b : ZMod height) + ((K - 1 : ℕ) : ZMod height)) =
        ((b + K - 1 : ℕ) : ZMod height) := by
      rw [show b + K - 1 = b + (K - 1) by omega]; push_cast; ring
    simp only at hx hy ⊢
    rw [hx, hy,
      torusArcRectangle_eq_torusContiguousRectangle (a + L) (b + K - 1) L K hL hK
        (by omega) (by omega)]
  -- Identify the reference edge with the lemma's distinguished edge.
  have hedge : horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K =
      torusRightEdge (((a + L - 1 : ℕ) : ZMod width), ((b + K - 1 : ℕ) : ZMod height)) := by
    rw [horizontalStaircaseReferenceEdge]
    congr 2
    · rw [show a + L - 1 = a + (L - 1) by omega]; push_cast; ring
    · rw [show b + K - 1 = b + (K - 1) by omega]; push_cast; ring
  rw [hleft, hright, hedge]
  exact isCrossingEdge_horizontalStaircase A hL hK ha0 haw hbh g

/-- The reference edge is a boundary edge of the left end window: it is the unique crossing edge
of the two end windows, hence a boundary edge of the left window.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 4. -/
theorem isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height) :
    IsRegionBoundaryEdge (G := torusGraph width height)
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
      (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K) :=
  ((isCrossingEdge_horizontalStaircaseEndWindows A hL hK ha0 haw hbh _).mpr rfl).1

/-- The reference edge is a boundary edge of the right end window.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 4. -/
theorem isRegionBoundaryEdge_horizontalStaircaseRightWindow_referenceEdge
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height) :
    IsRegionBoundaryEdge (G := torusGraph width height)
      (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K)
      (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K) :=
  ((isCrossingEdge_horizontalStaircaseEndWindows A hL hK ha0 haw hbh _).mpr rfl).2

/-! ### The reference edge is interior to the end pair

The reference edge has one endpoint in each end window, so both endpoints lie in the end pair
`S = W_0 ⊔ W_{L+K-1}`.  An edge with both endpoints in a region is not a boundary edge of that
region: `e` is the single interior bond of `S`, the bond summed over when the two windows are
contracted together.  This is what distinguishes the single-crossing pairing from the
complement inversions of the earlier steps — the only virtual leg shared by the two windows is
`e`, every other open leg crossing the boundary of `S`. -/

/-- **The reference edge is interior to the end pair.**

The reference edge `e` is *not* a boundary edge of the staircase end pair
`S = horizontalStaircaseEndPair`: it crosses between the two end windows
(`isCrossingEdge_horizontalStaircaseEndWindows`), so each endpoint lies in one of the windows,
hence in `S`.  An edge with both endpoints in `S` is not a boundary edge of `S`.  Thus `e` is
the single interior bond of `S`, summed over in the end-pair contraction.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex` (the single bond `e` joining the two windows);
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 4. -/
theorem not_isRegionBoundaryEdge_horizontalStaircaseEndPair_referenceEdge
    {L K a b : ℕ} (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height) :
    ¬ IsRegionBoundaryEdge (G := torusGraph width height)
        (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K)
        (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K) := by
  set e := horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K with he
  -- The end pair contains each end window.
  have hsubL : horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K ⊆
      horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K :=
    horizontalStaircaseLeftWindow_subset_endPair _
  have hsubR : horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K ⊆
      horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K :=
    horizontalStaircaseRightWindow_subset_endPair _
  -- The two endpoints of `e`: the lower one in the left window, the upper one in the right.
  have hep := torusRightEdge_endpoints_of_lt
    (p := ((a : ZMod width) + ((L - 1 : ℕ) : ZMod width), (b : ZMod height) +
      ((K - 1 : ℕ) : ZMod height)))
    (width := width) (height := height)
    (by rw [show (a : ZMod width) + ((L - 1 : ℕ) : ZMod width) = ((a + L - 1 : ℕ) : ZMod width)
          by rw [show a + L - 1 = a + (L - 1) by omega]; push_cast; ring,
        ZMod.val_natCast_of_lt (by omega)]; omega)
  -- The lower endpoint `e.1.1 = (a + L - 1, b + K - 1)` lies in the left window.
  have hin1 : e.1.1 ∈ horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K := by
    rw [he, horizontalStaircaseReferenceEdge, hep.1, horizontalStaircaseLeftWindow,
      mem_torusArcRectangle]
    refine ⟨?_, ?_⟩
    · rw [add_sub_cancel_left, ZMod.val_natCast_of_lt (by omega)]; omega
    · rw [add_sub_cancel_left, ZMod.val_natCast_of_lt (by omega)]; omega
  -- The upper endpoint `e.1.2 = (a + L, b + K - 1)` lies in the right window.
  have hin2 : e.1.2 ∈ horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K := by
    rw [he, horizontalStaircaseReferenceEdge, hep.2, horizontalStaircaseRightWindow,
      mem_torusArcRectangle]
    refine ⟨?_, ?_⟩
    · -- The horizontal distance from the right window's start `a + L` is `0`.
      have hLcast : ((L - 1 : ℕ) : ZMod width) + 1 = (L : ZMod width) := by
        rw [show (L : ZMod width) = ((L - 1 + 1 : ℕ) : ZMod width) by congr 1; omega]
        push_cast; ring
      rw [show ((a : ZMod width) + ((L - 1 : ℕ) : ZMod width) + 1) - ((a : ZMod width) +
            (L : ZMod width)) = (0 : ZMod width) by rw [← hLcast]; ring,
        ZMod.val_zero]; omega
    · -- The vertical distance from the right window's start `b + K - 1` is `0`.
      rw [show ((b : ZMod height) + ((K - 1 : ℕ) : ZMod height)) - ((b : ZMod height) +
            ((K - 1 : ℕ) : ZMod height)) = (0 : ZMod height) by ring, ZMod.val_zero]; omega
  -- An edge with both endpoints in `S` is not a boundary edge of `S`.
  rintro (⟨_, hout⟩ | ⟨hout, _⟩)
  · exact hout (hsubR hin2)
  · exact hout (hsubL hin1)

end Torus

end PEPS
end TNLean

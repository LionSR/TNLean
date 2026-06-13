import TNLean.PEPS.TorusDeformedWindow

/-!
# The overlapping-window patch and the staircase corner geometry

The two-dimensional strengthening of the normal PEPS Fundamental Theorem
(arXiv:1804.04964, the corollary at lines 2297--2318 of
`Papers/1804.04964/paper_normal.tex`) chains the consecutive-window comparisons of
`TNLean/PEPS/TorusDeformedWindow.lean` across the staircase patch around a lattice
edge, then strips the patch down to the two end windows by completing and inverting
the corner block.  This file is the geometry of that chaining and stripping, scoped
in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Steps 2--3.

## The staircase patch and the corner block

Around a horizontal edge with left endpoint `(x, y)` the overlapping-window chain
runs through `L + K` windows: `L + 1` horizontal slides across the edge followed by
`K - 1` vertical descents.  In the staircase coordinates `a = x - L + 1`,
`b = y - K + 1` the end pair is

* the left/last window `W_{L+K-1} = [a, a + L) × [b, b + K)` and
* the right/first window `W_0 = [a + L, a + 2L) × [b + K - 1, b + 2K - 1)`,

the diagonally offset pair of `TNLean/PEPS/TorusWindowRegion.lean`.  The patch
`P = ⋃_j W_j` is the union of the full horizontal band
`[a, a + 2L) × [b + K - 1, b + 2K - 1)` (the `2L × K` rectangle the horizontal
slides sweep) and the left vertical band `[a, a + L) × [b, b + 2K - 1)` (the
`L × (2K - 1)` rectangle the vertical descents sweep).  The difference
`P \ S` of the patch and the end pair is the single corner block
`[a, a + L) × [b + K, b + 2K - 1)` of size `L × (K - 1)`, and completing it with
one added row forms the injective `L × K` rectangle
`[a, a + L) × [b + K, b + 2K)` — the completed rectangle the corner stripping
inverts.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, the corollary and
  proof sketch at lines 2296--2445 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964); the
  filled-in derivation in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
  Steps 2--3.
-/

namespace TNLean
namespace PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]

/-! ### The horizontal staircase patch

The patch around a horizontal edge, in the staircase coordinates `(a, b)` of the
end pair, is the union of the `2L × K` horizontal band and the `L × (2K - 1)`
vertical band.  Both bands are read as cyclic `torusArcRectangle`s, so the
construction transports across the torus seam unchanged. -/

/-- The horizontal staircase patch `P`: the union of the `2L × K` horizontal band
`[a, a + 2L) × [b + K - 1, b + 2K - 1)` and the `L × (2K - 1)` vertical band
`[a, a + L) × [b, b + 2K - 1)`, in the staircase coordinates `s = (a, b)` of the
end pair.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex` (the patch `P = ⋃_j W_j`);
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 2. -/
def horizontalStaircasePatch (s : TorusVertex width height) (L K : ℕ) :
    Finset (TorusVertex width height) :=
  torusArcRectangle (s.1, s.2 + ((K - 1 : ℕ) : ZMod height)) (2 * L) K ∪
    torusArcRectangle s L (2 * K - 1)

/-- The left/last end window `W_{L+K-1} = [a, a + L) × [b, b + K)` of the
horizontal staircase, in the staircase coordinates `s = (a, b)`. -/
def horizontalStaircaseLeftWindow (s : TorusVertex width height) (L K : ℕ) :
    Finset (TorusVertex width height) :=
  torusArcRectangle s L K

/-- The right/first end window `W_0 = [a + L, a + 2L) × [b + K - 1, b + 2K - 1)` of
the horizontal staircase, in the staircase coordinates `s = (a, b)`. -/
def horizontalStaircaseRightWindow (s : TorusVertex width height) (L K : ℕ) :
    Finset (TorusVertex width height) :=
  torusArcRectangle (s.1 + (L : ZMod width), s.2 + ((K - 1 : ℕ) : ZMod height)) L K

/-- The staircase end pair `S = W_0 ⊔ W_{L+K-1}`: the disjoint union of the two
end windows. -/
def horizontalStaircaseEndPair (s : TorusVertex width height) (L K : ℕ) :
    Finset (TorusVertex width height) :=
  horizontalStaircaseLeftWindow s L K ∪ horizontalStaircaseRightWindow s L K

/-- The corner block `P \ S = [a, a + L) × [b + K, b + 2K - 1)` of size
`L × (K - 1)`: the upper-left block the staircase comparison strips. -/
def horizontalStaircaseCorner (s : TorusVertex width height) (L K : ℕ) :
    Finset (TorusVertex width height) :=
  torusArcRectangle (s.1, s.2 + (K : ZMod height)) L (K - 1)

/-! ### The completed corner rectangle

Completing the `L × (K - 1)` corner block with one added row forms the `L × K`
cyclic rectangle `[a, a + L) × [b + K, b + 2K)`, which is an `L × K` window, hence
injective.  Its complement within the patch, after the chaining, is the staircase
end pair: inverting the completed rectangle strips the corner and the added row,
leaving the open-boundary equality on the end pair. -/

/-- The completed corner rectangle `[a, a + L) × [b + K, b + 2K)` of size `L × K`:
the corner block plus one added row.  An `L × K` cyclic rectangle, hence injective
under the window hypotheses.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex` (add two-two tensors in the corner and invert);
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 3. -/
def horizontalStaircaseCompletedCorner (s : TorusVertex width height) (L K : ℕ) :
    Finset (TorusVertex width height) :=
  torusArcRectangle (s.1, s.2 + (K : ZMod height)) L K

/-! ### Disjointness of the staircase end pair

The left window occupies the cyclic columns `[a, a + L)` and the right window the
cyclic columns `[a + L, a + 2L)`; at the size `2L + 1 ≤ width` these column ranges
do not overlap, so the two end windows are disjoint. -/

/-- The two end windows of the horizontal staircase are disjoint: their cyclic
column ranges `[a, a + L)` and `[a + L, a + 2L)` are disjoint at `2L + 1 ≤ width`.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 3. -/
theorem horizontalStaircaseEndPair_disjoint {L K : ℕ}
    (hxw : 2 * L ≤ width) (s : TorusVertex width height) :
    Disjoint (horizontalStaircaseLeftWindow s L K)
      (horizontalStaircaseRightWindow s L K) := by
  rw [Finset.disjoint_left]
  intro v hvL hvR
  rw [horizontalStaircaseLeftWindow, mem_torusArcRectangle] at hvL
  rw [horizontalStaircaseRightWindow, mem_torusArcRectangle] at hvR
  obtain ⟨hvLx, _⟩ := hvL
  obtain ⟨hvRx, _⟩ := hvR
  -- The right window's column distance shifts the left window's by `L`.
  rw [show (L : ZMod width) = ((L : ℕ) : ZMod width) by norm_cast,
    zmod_val_sub_shift width v.1 s.1 L (by omega)] at hvRx
  have hd := ZMod.val_lt (v.1 - s.1)
  rw [if_pos (by omega : (v.1 - s.1).val < L)] at hvRx
  omega

/-! ### Injectivity of the end windows and the completed corner

Each end window of the staircase is an `L × K` cyclic window, injective by the
one-orientation window hypotheses; the completed corner is the `L × K` cyclic
rectangle `[a, a + L) × [b + K, b + 2K)`, injective for the same reason.  These are
the injective regions the corner-stripping step inverts. -/

namespace NormalTorusArcWindowInjectivityHypotheses

variable {L K : ℕ} {κ : RegionInjectivityData (TorusVertex width height)}

/-- The left/last end window is injective: it is an `L × K` cyclic window.

Source: arXiv:1804.04964, the corollary at lines 2297--2318 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 3. -/
theorem horizontalStaircaseLeftWindow_injective
    (h : NormalTorusArcWindowInjectivityHypotheses L K κ) (s : TorusVertex width height) :
    κ.IsInjective (horizontalStaircaseLeftWindow s L K) :=
  h.arcWindow_injective s

/-- The right/first end window is injective: it is an `L × K` cyclic window.

Source: arXiv:1804.04964, the corollary at lines 2297--2318 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 3. -/
theorem horizontalStaircaseRightWindow_injective
    (h : NormalTorusArcWindowInjectivityHypotheses L K κ) (s : TorusVertex width height) :
    κ.IsInjective (horizontalStaircaseRightWindow s L K) :=
  h.arcWindow_injective _

/-- The completed corner rectangle is injective: it is the `L × K` cyclic rectangle
`[a, a + L) × [b + K, b + 2K)`, an `L × K` window.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex` (the completed rectangle is injective);
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 3. -/
theorem horizontalStaircaseCompletedCorner_injective
    (h : NormalTorusArcWindowInjectivityHypotheses L K κ) (s : TorusVertex width height) :
    κ.IsInjective (horizontalStaircaseCompletedCorner s L K) :=
  h.arcWindow_injective _

end NormalTorusArcWindowInjectivityHypotheses

/-! ### The patch decomposition

The patch `P` splits as the disjoint union of the end pair `S` and the corner block.
This is the load-bearing geometry of Step 3: the corner is exactly `P \ S`, the
single block that must be completed and inverted to strip the patch equality down to
the end pair.  The decomposition needs the no-wraparound bounds `2L ≤ width`,
`2K ≤ height` so that the row and column shifts compose without crossing the seam. -/

/-- The corner block is disjoint from the end pair: the corner occupies the cyclic
rows `[b + K, b + 2K - 1)`, the left end window the rows `[b, b + K)`, and the right
end window the columns `[a + L, a + 2L)`, all disjoint from the corner's columns
`[a, a + L)` and rows at the size bounds.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 3. -/
theorem horizontalStaircaseCorner_disjoint_endPair {L K : ℕ} (hK : 0 < K)
    (hxw : 2 * L ≤ width) (hyh : 2 * K ≤ height) (s : TorusVertex width height) :
    Disjoint (horizontalStaircaseEndPair s L K) (horizontalStaircaseCorner s L K) := by
  rw [Finset.disjoint_left]
  intro v hvS hvC
  rw [horizontalStaircaseCorner, mem_torusArcRectangle] at hvC
  simp only at hvC
  obtain ⟨hvCx, hvCy⟩ := hvC
  -- The corner's row distance shifts `s.2`'s by `K`.
  rw [show (K : ZMod height) = ((K : ℕ) : ZMod height) by norm_cast,
    zmod_val_sub_shift height v.2 s.2 K (by omega)] at hvCy
  have hdy := ZMod.val_lt (v.2 - s.2)
  rw [horizontalStaircaseEndPair, Finset.mem_union] at hvS
  rcases hvS with hvL | hvR
  · rw [horizontalStaircaseLeftWindow, mem_torusArcRectangle] at hvL
    obtain ⟨_, hvLy⟩ := hvL
    -- The left window has row distance `< K`; the corner's shifts past `K`, so the
    -- corner row distance wraps and exceeds `K - 1`.
    rw [if_pos (by omega : (v.2 - s.2).val < K)] at hvCy
    omega
  · rw [horizontalStaircaseRightWindow, mem_torusArcRectangle] at hvR
    obtain ⟨hvRx, _⟩ := hvR
    -- The right window has column distance `≥ L`; the corner has `< L`.
    rw [show (L : ZMod width) = ((L : ℕ) : ZMod width) by norm_cast,
      zmod_val_sub_shift width v.1 s.1 L (by omega)] at hvRx
    have hdx := ZMod.val_lt (v.1 - s.1)
    rw [if_pos (by omega : (v.1 - s.1).val < L)] at hvRx
    omega

/-- **The patch decomposition.** The horizontal staircase patch `P` is the union of
the end pair `S` and the corner block: `P = S ∪ corner`.  With the disjointness
`horizontalStaircaseCorner_disjoint_endPair` this gives `P \ S = corner`, the single
block the corner stripping completes and inverts.  The no-wraparound bounds
`2L ≤ width`, `2K ≤ height` keep every row and column shift clear of the seam.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex` (the patch and its corner block);
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 3. -/
theorem horizontalStaircasePatch_eq_endPair_union_corner {L K : ℕ} (hL : 0 < L)
    (hK : 0 < K) (hxw : 2 * L ≤ width) (hyh : 2 * K ≤ height)
    (s : TorusVertex width height) :
    horizontalStaircasePatch s L K =
      horizontalStaircaseEndPair s L K ∪ horizontalStaircaseCorner s L K := by
  ext v
  rw [horizontalStaircasePatch, horizontalStaircaseEndPair, horizontalStaircaseLeftWindow,
    horizontalStaircaseRightWindow, horizontalStaircaseCorner, Finset.mem_union, Finset.mem_union,
    Finset.mem_union, mem_torusArcRectangle, mem_torusArcRectangle, mem_torusArcRectangle,
    mem_torusArcRectangle, mem_torusArcRectangle]
  simp only
  -- Reduce every shifted row/column distance to the base distances from `s`.
  rw [show (L : ZMod width) = ((L : ℕ) : ZMod width) by norm_cast,
    show ((K - 1 : ℕ) : ZMod height) = ((K - 1 : ℕ) : ZMod height) from rfl,
    show (K : ZMod height) = ((K : ℕ) : ZMod height) by norm_cast,
    zmod_val_sub_shift width v.1 s.1 L (by omega),
    zmod_val_sub_shift height v.2 s.2 (K - 1) (by omega),
    zmod_val_sub_shift height v.2 s.2 K (by omega)]
  have hdx := ZMod.val_lt (v.1 - s.1)
  have hdy := ZMod.val_lt (v.2 - s.2)
  constructor
  · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
    · -- Horizontal band: split on whether the row distance is below `K - 1`.
      split_ifs at hy with hc
      · -- A wrapped row: the corner's top, in the corner block.
        right
        rw [if_pos (by omega : (v.2 - s.2).val < K)]; omega
      · -- An unwrapped row in `[b + K - 1, b + 2K - 1)`: split on the column.
        by_cases hcx : (v.1 - s.1).val < L
        · -- Left columns at this row: either the corner or the left window bottom.
          by_cases hrow : (v.2 - s.2).val < K
          · exact Or.inl (Or.inl ⟨hcx, hrow⟩)
          · right; rw [if_neg (by omega : ¬ (v.2 - s.2).val < K)]; omega
        · -- Right columns at this row: the right window.
          left; right
          refine ⟨?_, ?_⟩
          · rw [if_neg hcx]; omega
          · rw [if_neg (by omega : ¬ (v.2 - s.2).val < K - 1)]; omega
    · -- Vertical band: split on whether the row distance reaches `K`.
      by_cases hrow : (v.2 - s.2).val < K
      · exact Or.inl (Or.inl ⟨hx, hrow⟩)
      · right; rw [if_neg (by omega : ¬ (v.2 - s.2).val < K)]; omega
  · rintro ((⟨hx, hy⟩ | ⟨hx, hy⟩) | ⟨hx, hy⟩)
    · -- Left window: in the vertical band.
      right; exact ⟨hx, by omega⟩
    · -- Right window: in the horizontal band.
      split_ifs at hx with hcx
      · omega
      · left; refine ⟨by omega, ?_⟩
        split_ifs at hy with hcy
        · omega
        · rw [if_neg (by omega : ¬ (v.2 - s.2).val < K - 1)]; omega
    · -- Corner block: in the horizontal band.
      split_ifs at hy with hcy
      · omega
      · left; refine ⟨by omega, ?_⟩
        rw [if_neg (by omega : ¬ (v.2 - s.2).val < K - 1)]; omega

/-- **The corner is the patch difference of the end pair.** `P \ S = corner`: the
single block the corner stripping completes and inverts.  Immediate from the patch
decomposition `P = S ∪ corner` and the disjointness of the corner from the end pair.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 3. -/
theorem horizontalStaircasePatch_sdiff_endPair {L K : ℕ} (hL : 0 < L) (hK : 0 < K)
    (hxw : 2 * L ≤ width) (hyh : 2 * K ≤ height) (s : TorusVertex width height) :
    horizontalStaircasePatch s L K \ horizontalStaircaseEndPair s L K =
      horizontalStaircaseCorner s L K := by
  rw [horizontalStaircasePatch_eq_endPair_union_corner hL hK hxw hyh s,
    Finset.union_sdiff_left,
    Finset.sdiff_eq_self_of_disjoint
      (horizontalStaircaseCorner_disjoint_endPair hK hxw hyh s).symm]

end PEPS
end TNLean

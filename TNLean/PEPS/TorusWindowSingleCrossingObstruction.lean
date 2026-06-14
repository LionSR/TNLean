import TNLean.PEPS.TorusWindowComplement

/-!
# The single-crossing pair spans a full double-width band at its shared row

The two-dimensional strengthening of the normal PEPS Fundamental Theorem
(arXiv:1804.04964, the corollary at lines 2297--2318 of
`Papers/1804.04964/paper_normal.tex`) extracts a bond operator on one lattice
edge by comparing two diagonally offset `L × K` windows that cross at exactly that
edge (`isCrossingEdge_horizontalStaircase`).  A natural route to the per-edge
multiplicativity would feed those two windows as the red and blue blocks of a
coarse three-block frame, with the third block their torus complement, and read
the multiplicativity off the coarse three-site comparison.  That route needs the
third block --- the complement of the two-window union --- to be injective.

This file records why that complement is **not** injective under the
one-orientation `L × K` window hypotheses at the corollary's minimal width
`2L + 1`, and why the obstruction is intrinsic to the single-crossing geometry
rather than a feature of one particular window pair.  The load-bearing fact is
purely combinatorial: two `L × K` windows cross at a single lattice edge only
when they are column-adjacent across one shared row, and then their union covers
**all** `2L` consecutive columns at that shared row.  At width `2L + 1` the
complement therefore has a band of width `1` at that row, below the `L` columns
any `L × K` window translate needs; the complement is not a union of injective
window translates, so its blocked tensor is not injective from the hypotheses
alone.

The conclusion is the geometric verdict on the per-edge coarse-frame route: a
single-crossing `L × K` pair never has an injective complement at the minimal
width, because single crossing forces the diagonal offset, the offset forces the
double-width row span, and the double-width row span forces the sub-`L`
complement band.  The faithful route to the per-edge operator is therefore the
shared-corner cancellation of the overlapping-window chain, which inverts only
single windows and consecutive-window unions, never the two-window complement.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964, the
  corollary and proof sketch at lines 2296--2445 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964); the
  filled-in derivation and the obstruction in
  `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 3 ("The complement of the
  end pair is not injective at the minimal size").
-/

namespace TNLean
namespace PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]

/-! ### The shared row of the single-crossing pair

The left window `[a, a + L) × [b, b + K)` and the right window
`[a + L, a + 2L) × [b + K - 1, b + 2K - 1)` of the staircase pair share exactly
one row, `b + K - 1`: it is the top row of the left window and the bottom row of
the right window.  At that row the left window occupies columns `[a, a + L)` and
the right window the columns `[a + L, a + 2L)`, so their union occupies the
contiguous `2L` columns `[a, a + 2L)`.  This is the obstruction band of Step 3:
its torus complement at that row is the `width - 2L` columns outside it, which is
a single column at the minimal width `2L + 1`. -/

/-- **The single-crossing pair covers a full double-width row band.**

At the shared row `b + K - 1` every column in the contiguous range `[a, a + 2L)`
lies in the union of the two staircase end windows: columns `[a, a + L)` in the
left window and columns `[a + L, a + 2L)` in the right window.  This is the
double-width span behind the minimal-width obstruction: the complement band at
this row is `width - 2L` columns wide, a single column at `width = 2L + 1`.

The windows are read as wraparound-free contiguous rectangles, the convention of
`isCrossingEdge_horizontalStaircase`; the `hK` hypothesis fixes the shared row at
`b + K - 1` (the top row `b + K - 1` of the left window, the bottom row of the
right window).

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex`; the obstruction in
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 3. -/
theorem horizontalStaircasePair_row_span {L K a b : ℕ} (hK : 0 < K)
    {c : ℕ} (hc0 : a ≤ c) (hc1 : c < a + 2 * L)
    (v : TorusVertex width height)
    (hvx : v.1.val = c) (hvy : v.2.val = b + K - 1) :
    v ∈ (torusContiguousRectangle a b L K :
        Finset (TorusVertex width height)) ∪
      torusContiguousRectangle (a + L) (b + K - 1) L K := by
  rw [Finset.mem_union, mem_torusContiguousRectangle, mem_torusContiguousRectangle]
  rcases lt_or_ge c (a + L) with hcL | hcL
  · -- The left window covers the columns `[a, a + L)` at its top row `b + K - 1`.
    exact Or.inl ⟨by omega, by omega, by omega, by omega⟩
  · -- The right window covers the columns `[a + L, a + 2L)` at its bottom row.
    exact Or.inr ⟨by omega, by omega, by omega, by omega⟩

/-! ### The complement is below window width at the shared row

At width `2L + 1` the complement of the union, at the shared row, is a single
column.  Any `L × K` window translate that contains a complement vertex of that
row must include `L` consecutive cyclic columns through that row; but every cyclic
column at that row except the one complement column lies in the union, so no
window translate fits.  We record the column count directly: the union meets
every cyclic column at the shared row except those in `[a + 2L, width)`, which is
`width - 2L = 1` column at the minimal width. -/

/-- **The complement band at the shared row is below window width at the minimal
width.**

At the minimal width `2L + 1` the cyclic columns of the shared row split into the
`2L` columns `[a, a + 2L)` of the union and the single column `a + 2L = a - 1`
(mod `width`) outside it.  A window translate needs `L` consecutive columns
through the row, but only one column outside the union remains, so for `2 ≤ L`
no `L × K` window translate avoids the union at this row.  This is the precise
sense in which the union complement is not a union of injective window
translates: the obstruction is a column count, `width - 2L < L`.

The statement is the column-count form of the obstruction: whenever the union
occupies `2L` columns (`2L ≤ width`) and the width is below `3L`, in particular
at the minimal width `2L + 1`, the columns outside the union number `width - 2L`,
strictly below the `L` columns any window translate needs.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex`; the obstruction in
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 3. -/
theorem horizontalStaircasePair_complement_band_lt_window {L width : ℕ}
    (haw : 2 * L ≤ width) (hwidth : width < 3 * L) :
    width - 2 * L < L := by
  omega

/-! ### No window translate fits through the complement at the shared row

The decisive form of the obstruction: at the minimal width every wraparound-free
`L × K` window translate whose rows include the shared row `b + K - 1` meets the
union.  A window translate at start `(p, q)` covers columns `[p, p + L)`; to avoid
the union at the shared row it would need `[p, p + L)` disjoint from `[a, a + 2L)`,
forcing `p + L ≤ a` or `a + 2L ≤ p`.  With `2L ≤ p` ruled out by the width
(`p + L ≤ width < 3L ≤ a + 2L + L` and `a ≤ p` would push past the seam) and
`p + L ≤ a` ruled out below, no such translate exists.  Hence the complement of
the union, nonempty at the shared row, is not covered by injective window
translates, and its blocked tensor is not injective from the one-orientation
hypotheses alone --- the precise obstruction to the per-edge coarse-frame route. -/

/-- **Every window translate through the shared row meets the single-crossing
union, at the minimal width.**

A wraparound-free `L × K` window translate at start `(p, q)` with `a ≤ p`,
`p + L ≤ width`, whose row range includes the shared row `b + K - 1`
(`q ≤ b + K - 1 < q + K`), meets the staircase union when the width is below `3L`
and the union sits at `a + 2L ≤ width`.  The reason is the double-width row span:
the window's columns `[p, p + L)` and the union's columns `[a, a + 2L)` both lie
in `[a, width)`, and at width below `3L` they cannot be disjoint --- there is no
room for `L` further columns after the union's `2L`.  This is why no injective
window translate fits through the complement at the shared row.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex`; the obstruction in
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 3. -/
theorem horizontalStaircasePair_window_meets_row {L K a b p q : ℕ} (hK : 0 < K)
    (haw : a + 2 * L ≤ width) (hwidth : width < a + 3 * L)
    (hbh : b + K ≤ height) (hap : a ≤ p) (hpw : p + L ≤ width)
    (hq0 : q ≤ b + K - 1) (hq1 : b + K - 1 < q + K) :
    ∃ v : TorusVertex width height,
      v ∈ (torusContiguousRectangle p q L K :
          Finset (TorusVertex width height)) ∧
        v ∈ (torusContiguousRectangle a b L K ∪
          torusContiguousRectangle (a + L) (b + K - 1) L K) := by
  -- The window column range `[p, p + L)` cannot escape the union's `[a, a + 2L)`
  -- at width below `a + 3L`: with `a ≤ p` and `p + L ≤ width < a + 3L`, the
  -- column `p` lies in both, since `a ≤ p < a + 2L`.
  have hp2L : p < a + 2 * L := by omega
  -- The witness vertex sits at column `p`, shared row `b + K - 1`.
  obtain ⟨vx, hvx⟩ : ∃ vx : ZMod width, vx.val = p :=
    ⟨(p : ZMod width), ZMod.val_natCast_of_lt (by omega)⟩
  obtain ⟨vy, hvy⟩ : ∃ vy : ZMod height, vy.val = b + K - 1 :=
    ⟨((b + K - 1 : ℕ) : ZMod height), ZMod.val_natCast_of_lt (by omega)⟩
  refine ⟨(vx, vy), ?_, ?_⟩
  · -- In the window translate: column `p ∈ [p, p + L)`, row `b + K - 1 ∈ [q, q + K)`.
    rw [mem_torusContiguousRectangle]
    simp only [hvx, hvy]
    refine ⟨by omega, by omega, by omega, by omega⟩
  · -- In the union: column `p ∈ [a, a + 2L)` at the shared row.
    exact horizontalStaircasePair_row_span hK hap hp2L (vx, vy) hvx hvy

/-! ### The single-crossing union is not a cyclic rectangle

The landed complement-injectivity machinery delivers an injective torus complement
only for a single cyclic rectangle `torusArcRectangle s w h` (`width - w` band and
`w × (height - h)` leftover, both injective at `w ≤ width - L`, `h ≤ height - K`).
The staircase union is **never** such a rectangle, so its complement is outside the
reach of that machinery.  The reason is the product structure of a cyclic
rectangle: its membership is a column condition AND a row condition read
independently, so it is closed under "swapping coordinates" between two of its
vertices.  The union contains the three corner vertices `(a, b + K - 1)`,
`(a + 2L - 1, b + K - 1)`, `(a, b)`, but **not** the swapped vertex
`(a + 2L - 1, b)` (column `a + 2L - 1` outside the left window's columns, row `b`
outside the right window's rows for `2 ≤ K`).  A cyclic rectangle containing the
three corners would contain the swapped one too, so the union is not a cyclic
rectangle. -/

/-- **The single-crossing union is not a cyclic rectangle.**

For `2 ≤ K` and `2 ≤ L`, with the union sitting wraparound-free
(`a + 2L ≤ width`, `b + 2K - 1 ≤ height`, `1 ≤ a`, `1 ≤ b`), the union of the two
staircase end windows is not equal to any cyclic torus rectangle
`torusArcRectangle s w h`.  The product structure of a cyclic rectangle forces the
swapped corner `(a + 2L - 1, b)` to belong whenever the three corners
`(a, b + K - 1)`, `(a + 2L - 1, b + K - 1)`, `(a, b)` do; but the swapped corner is
outside the union (its column lies only in the right window, its row only in the
left).  This is the structural reason the union complement is beyond the landed
rectangle-complement injectivity, and hence the per-edge coarse-frame route has no
injective third block at the minimal width.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex`; the obstruction in
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 3. -/
theorem horizontalStaircasePair_ne_arcRectangle {L K a b : ℕ} (hL : 2 ≤ L)
    (hK : 2 ≤ K) (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (s : TorusVertex width height) (w h : ℕ) :
    (torusContiguousRectangle a b L K : Finset (TorusVertex width height)) ∪
        torusContiguousRectangle (a + L) (b + K - 1) L K ≠
      torusArcRectangle s w h := by
  intro heq
  -- The three corner vertices of the union, at columns `a`, `a + 2L - 1` and rows
  -- `b + K - 1`, `b`.
  obtain ⟨xa, hxa⟩ : ∃ xa : ZMod width, xa.val = a :=
    ⟨(a : ZMod width), ZMod.val_natCast_of_lt (by omega)⟩
  obtain ⟨xr, hxr⟩ : ∃ xr : ZMod width, xr.val = a + 2 * L - 1 :=
    ⟨((a + 2 * L - 1 : ℕ) : ZMod width), ZMod.val_natCast_of_lt (by omega)⟩
  obtain ⟨yt, hyt⟩ : ∃ yt : ZMod height, yt.val = b + K - 1 :=
    ⟨((b + K - 1 : ℕ) : ZMod height), ZMod.val_natCast_of_lt (by omega)⟩
  obtain ⟨yb, hyb⟩ : ∃ yb : ZMod height, yb.val = b :=
    ⟨(b : ZMod height), ZMod.val_natCast_of_lt (by omega)⟩
  -- The three corners are in the union, hence in the rectangle.
  have hmem : ∀ {v : TorusVertex width height},
      v ∈ (torusContiguousRectangle a b L K ∪
          torusContiguousRectangle (a + L) (b + K - 1) L K :
            Finset (TorusVertex width height)) →
        (v.1 - s.1).val < w ∧ (v.2 - s.2).val < h := by
    intro v hv
    rw [heq, mem_torusArcRectangle] at hv; exact hv
  -- Corner `(xa, yt) = (a, b + K - 1)`: left window's top-left, in the union.
  have hAT := hmem (v := (xa, yt)) (by
    simp only [Finset.mem_union, mem_torusContiguousRectangle]
    refine Or.inl ⟨?_, ?_, ?_, ?_⟩ <;> simp only [hxa, hyt] <;> omega)
  -- Corner `(xr, yt) = (a + 2L - 1, b + K - 1)`: right window's bottom-right.
  have hRT := hmem (v := (xr, yt)) (by
    simp only [Finset.mem_union, mem_torusContiguousRectangle]
    refine Or.inr ⟨?_, ?_, ?_, ?_⟩ <;> simp only [hxr, hyt] <;> omega)
  -- Corner `(xa, yb) = (a, b)`: left window's bottom-left.
  have hAB := hmem (v := (xa, yb)) (by
    simp only [Finset.mem_union, mem_torusContiguousRectangle]
    refine Or.inl ⟨?_, ?_, ?_, ?_⟩ <;> simp only [hxa, hyb] <;> omega)
  -- The swapped corner `(xr, yb) = (a + 2L - 1, b)` satisfies the rectangle's
  -- column condition (from `hRT`) and row condition (from `hAB`), so it is in the
  -- rectangle, hence in the union.
  have hswap : ((xr, yb) : TorusVertex width height) ∈
      (torusContiguousRectangle a b L K ∪
        torusContiguousRectangle (a + L) (b + K - 1) L K :
          Finset (TorusVertex width height)) := by
    rw [heq]
    simp only [mem_torusArcRectangle]
    exact ⟨hRT.1, hAB.2⟩
  -- But `(a + 2L - 1, b)` is in neither window: its column is outside the left
  -- window (`a + 2L - 1 ≥ a + L`) and its row is outside the right window
  -- (`b < b + K - 1` for `2 ≤ K`).
  simp only [Finset.mem_union, mem_torusContiguousRectangle] at hswap
  rcases hswap with ⟨_, hxlt, _, _⟩ | ⟨_, _, hylo, _⟩
  · simp only [hxr] at hxlt; omega
  · simp only [hyb] at hylo; omega

end PEPS
end TNLean

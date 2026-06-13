import TNLean.PEPS.TorusWindowExtraction

/-!
# The boundary of the staircase end pair is the windows' external legs

The two-dimensional strengthening of the normal PEPS Fundamental Theorem
(arXiv:1804.04964, the corollary at lines 2297--2318 of
`Papers/1804.04964/paper_normal.tex`) extracts the bond operator on the distinguished edge `e`
from the open-boundary end-pair equality `staircasePair_insert_eq_open` of
`TNLean/PEPS/TorusWindowChain6.lean` (Step 4 of the proof sketch).  The extraction rests on the
*single-crossing* geometry: `e` is the only lattice edge joining the two end windows, hence the
only interior bond of the end pair `S = W_0 ⊔ W_{L+K-1}`, with every other open leg of each
window crossing the boundary of `S`.

The landed single-crossing lemmas of `TNLean/PEPS/TorusWindowExtraction.lean` supply one
direction: a boundary edge of an end window other than `e` is a boundary edge of `S`
(`isRegionBoundaryEdge_endPair_of_leftWindow`, `isRegionBoundaryEdge_endPair_of_rightWindow`).
This file supplies the converse and assembles the complete characterization: every boundary edge
of `S` is a boundary edge of exactly one of the two windows and is not `e`.  Together with the
interiority of `e` (`not_isRegionBoundaryEdge_horizontalStaircaseEndPair_referenceEdge`), this
exhibits the boundary `∂S` as the disjoint union of the two windows' external legs with `e` the
single interior bond.  This characterization is the geometric peeling that turns the end-pair
`RegionInsert` equality into a relation across the single bond `e`: the open legs of `S` are
partitioned into the left window's external legs and the right window's external legs, and the
only leg the two windows share is `e`, summed over in the end-pair contraction.

The window the boundary edge of `S` belongs to is read off the in-region endpoint: the endpoint
of `f` that lies in `S` lies in exactly one window (the two end windows are disjoint at
`2 * L ≤ width`), and the out-of-`S` endpoint lies outside that window since it lies outside all
of `S`.  The two windows being disjoint, no boundary edge of `S` is a boundary edge of both
windows, so the partition is genuine.

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

/-! ### A boundary edge of the end pair belongs to one window

The in-region endpoint of a boundary edge of `S` lies in one of the two end windows; the
out-of-region endpoint lies outside that window since it lies outside all of `S`.  This makes the
edge a boundary edge of that window. -/

omit [Fact (1 < width)] [Fact (1 < height)] in
/-- A vertex outside the end pair is outside the left end window. -/
private theorem notMem_leftWindow_of_notMem_endPair {L K : ℕ} {s : TorusVertex width height}
    {v : TorusVertex width height} (hv : v ∉ horizontalStaircaseEndPair s L K) :
    v ∉ horizontalStaircaseLeftWindow s L K :=
  fun hL => hv (horizontalStaircaseLeftWindow_subset_endPair s hL)

omit [Fact (1 < width)] [Fact (1 < height)] in
/-- A vertex outside the end pair is outside the right end window. -/
private theorem notMem_rightWindow_of_notMem_endPair {L K : ℕ} {s : TorusVertex width height}
    {v : TorusVertex width height} (hv : v ∉ horizontalStaircaseEndPair s L K) :
    v ∉ horizontalStaircaseRightWindow s L K :=
  fun hR => hv (horizontalStaircaseRightWindow_subset_endPair s hR)

/-- **A boundary edge of the end pair is a boundary edge of one of the two windows.**

A boundary edge `f` of the staircase end pair `S = W_0 ⊔ W_{L+K-1}` is a boundary edge of the
left end window or of the right end window: the in-region endpoint of `f` lies in `S`, hence in
one of the two windows, while the out-of-region endpoint lies outside all of `S`, hence outside
that window.  This is the converse of the landed
`isRegionBoundaryEdge_endPair_of_leftWindow` / `...rightWindow`.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex` (the external legs of the two windows are the boundary of the
end pair); `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 4. -/
theorem isRegionBoundaryEdge_window_of_endPair {L K : ℕ} {s : TorusVertex width height}
    {f : Edge (torusGraph width height)}
    (hf : IsRegionBoundaryEdge (G := torusGraph width height)
      (horizontalStaircaseEndPair s L K) f) :
    IsRegionBoundaryEdge (G := torusGraph width height)
        (horizontalStaircaseLeftWindow s L K) f ∨
      IsRegionBoundaryEdge (G := torusGraph width height)
        (horizontalStaircaseRightWindow s L K) f := by
  rcases hf with ⟨hin, hout⟩ | ⟨hout, hin⟩
  · -- `f.1.1 ∈ S`, `f.1.2 ∉ S`.  Split on which window the in-endpoint lies in.
    rw [horizontalStaircaseEndPair, Finset.mem_union] at hin
    rcases hin with hinL | hinR
    · exact Or.inl (Or.inl ⟨hinL, notMem_leftWindow_of_notMem_endPair hout⟩)
    · exact Or.inr (Or.inl ⟨hinR, notMem_rightWindow_of_notMem_endPair hout⟩)
  · -- `f.1.2 ∈ S`, `f.1.1 ∉ S`.
    rw [horizontalStaircaseEndPair, Finset.mem_union] at hin
    rcases hin with hinL | hinR
    · exact Or.inl (Or.inr ⟨notMem_leftWindow_of_notMem_endPair hout, hinL⟩)
    · exact Or.inr (Or.inr ⟨notMem_rightWindow_of_notMem_endPair hout, hinR⟩)

/-! ### A boundary edge of the end pair is not the reference edge

The reference edge `e` is interior to `S` (both endpoints in `S`, one per window), so it is not a
boundary edge of `S`.  Hence every boundary edge of `S` differs from `e`. -/

/-- **A boundary edge of the end pair is not the reference edge.**

A boundary edge `f` of the staircase end pair `S` differs from the reference edge `e`: `e` has
both endpoints in `S` (one in each window), so `e` is interior to `S`
(`not_isRegionBoundaryEdge_horizontalStaircaseEndPair_referenceEdge`), while `f` is a boundary
edge of `S`.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex` (the single bond `e` is the only interior bond);
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 4. -/
theorem ne_referenceEdge_of_isRegionBoundaryEdge_endPair {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    {f : Edge (torusGraph width height)}
    (hf : IsRegionBoundaryEdge (G := torusGraph width height)
      (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K) f) :
    f ≠ horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K := by
  rintro rfl
  exact not_isRegionBoundaryEdge_horizontalStaircaseEndPair_referenceEdge hL hK ha0 haw hbh hf

/-! ### The complete characterization of the end pair's boundary

The boundary edges of `S` are exactly the boundary edges of the two windows other than the
reference edge `e`: an edge is a boundary edge of `S` if and only if it is a boundary edge of one
of the two windows and is not `e`.  This is the partition of the open legs of `S` into the two
windows' external legs, with `e` the single interior bond. -/

/-- **The boundary of the end pair is the windows' external legs.**

An edge `f` is a boundary edge of the staircase end pair `S = W_0 ⊔ W_{L+K-1}` if and only if it
is a boundary edge of one of the two end windows and differs from the reference edge `e`.  The
forward direction is `isRegionBoundaryEdge_window_of_endPair` together with
`ne_referenceEdge_of_isRegionBoundaryEdge_endPair`; the backward direction is the landed
`isRegionBoundaryEdge_endPair_of_leftWindow` / `...rightWindow`.  This exhibits `∂S` as the
disjoint union of the external legs of the two windows, with `e` the single interior bond summed
over in the end-pair contraction — the geometric peeling that turns the end-pair `RegionInsert`
equality into a relation across the single bond `e`.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex` (the external legs of the two windows are the boundary of the
end pair, `e` the single bond joining them); `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 4. -/
theorem isRegionBoundaryEdge_endPair_iff {L K a b : ℕ}
    (A : Tensor (torusGraph width height) d)
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (f : Edge (torusGraph width height)) :
    IsRegionBoundaryEdge (G := torusGraph width height)
        (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K) f ↔
      (IsRegionBoundaryEdge (G := torusGraph width height)
            (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K) f ∨
          IsRegionBoundaryEdge (G := torusGraph width height)
            (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K) f) ∧
        f ≠ horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K := by
  constructor
  · intro hf
    exact ⟨isRegionBoundaryEdge_window_of_endPair hf,
      ne_referenceEdge_of_isRegionBoundaryEdge_endPair hL hK ha0 haw hbh hf⟩
  · rintro ⟨hwin | hwin, hne⟩
    · exact isRegionBoundaryEdge_endPair_of_leftWindow A hL hK ha0 haw hbh hwin hne
    · exact isRegionBoundaryEdge_endPair_of_rightWindow A hL hK ha0 haw hbh hwin hne

/-! ### A boundary edge of the end pair lies on exactly one window

The reference edge `e` is a boundary edge of *both* windows (it is the crossing edge), but it is
*not* a boundary edge of `S`.  Every other edge that is a boundary edge of both windows is
likewise `e` (the single crossing).  Hence a boundary edge of `S` — which excludes `e` — is a
boundary edge of exactly one window: the partition of `∂S` into the two windows' external legs is
disjoint. -/

/-- **An edge that is a boundary edge of both end windows is the reference edge.**

The only edge that is a boundary edge of both the left and the right end window is the reference
edge `e`: a boundary edge of both is a crossing edge of the pair
(`IsCrossingEdge`), and the unique crossing edge is `e`
(`isCrossingEdge_horizontalStaircaseEndWindows`).  Conversely `e` is a boundary edge of each
window.  So the two windows' external legs meet only along `e`.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 4. -/
theorem eq_referenceEdge_of_isRegionBoundaryEdge_both_endWindows {L K a b : ℕ}
    (A : Tensor (torusGraph width height) d)
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    {f : Edge (torusGraph width height)}
    (hfL : IsRegionBoundaryEdge (G := torusGraph width height)
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K) f)
    (hfR : IsRegionBoundaryEdge (G := torusGraph width height)
      (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K) f) :
    f = horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K :=
  (isCrossingEdge_horizontalStaircaseEndWindows A hL hK ha0 haw hbh f).mp ⟨hfL, hfR⟩

/-- **A boundary edge of the end pair lies on exactly one window.**

A boundary edge `f` of the staircase end pair `S` is a boundary edge of exactly one of the two end
windows: it is a boundary edge of one (`isRegionBoundaryEdge_window_of_endPair`), and it is not a
boundary edge of both, since the only edge that is a boundary edge of both is the reference edge
`e` (`eq_referenceEdge_of_isRegionBoundaryEdge_both_endWindows`), which is not a boundary edge of
`S` (`ne_referenceEdge_of_isRegionBoundaryEdge_endPair`).  This is the disjointness of the
partition of `∂S` into the two windows' external legs.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 4. -/
theorem isRegionBoundaryEdge_endPair_exactlyOne_window {L K a b : ℕ}
    (A : Tensor (torusGraph width height) d)
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    {f : Edge (torusGraph width height)}
    (hf : IsRegionBoundaryEdge (G := torusGraph width height)
      (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K) f) :
    (IsRegionBoundaryEdge (G := torusGraph width height)
          (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K) f ∧
        ¬ IsRegionBoundaryEdge (G := torusGraph width height)
          (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K) f) ∨
      (¬ IsRegionBoundaryEdge (G := torusGraph width height)
          (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K) f ∧
        IsRegionBoundaryEdge (G := torusGraph width height)
          (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K) f) := by
  have hne : f ≠ horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K :=
    ne_referenceEdge_of_isRegionBoundaryEdge_endPair hL hK ha0 haw hbh hf
  -- `f` is a boundary edge of one window; were it a boundary edge of both, it would be `e`.
  rcases isRegionBoundaryEdge_window_of_endPair hf with hfL | hfR
  · refine Or.inl ⟨hfL, fun hfR => hne ?_⟩
    exact eq_referenceEdge_of_isRegionBoundaryEdge_both_endWindows A hL hK ha0 haw hbh hfL hfR
  · refine Or.inr ⟨fun hfL => hne ?_, hfR⟩
    exact eq_referenceEdge_of_isRegionBoundaryEdge_both_endWindows A hL hK ha0 haw hbh hfL hfR

/-! ### The complement of one window is the opposite window and the rest

The complement of one end window splits as the opposite end window joined with the complement of
the whole end pair: $\mathrm{univ}\setminus W_0 = W_{L+K-1}\sqcup(\mathrm{univ}\setminus S)$.  This
is the geometric fact behind the bond-$e$ coefficient identity: contracting one window against its
complement factors the contraction into the genuine block of the opposite window (the window the
bond $e$ joins to) and the rest of the torus.  Both windows being subsets of $S$, the splits hold
for either window, with the opposite window the difference $S\setminus W$. -/

omit [Fact (1 < width)] [Fact (1 < height)] in
/-- The difference of the end pair and the left window is the right window: at `2 * L ≤ width` the
two windows are disjoint, so removing the left window from `S = W_0 ∪ W_{L+K-1}` leaves the right
window. -/
theorem horizontalStaircaseEndPair_sdiff_leftWindow {L K : ℕ} (hxw : 2 * L ≤ width)
    (s : TorusVertex width height) :
    horizontalStaircaseEndPair s L K \ horizontalStaircaseLeftWindow s L K =
      horizontalStaircaseRightWindow s L K := by
  rw [horizontalStaircaseEndPair, Finset.union_sdiff_left,
    Finset.sdiff_eq_self_of_disjoint
      (horizontalStaircaseEndPair_disjoint hxw s).symm]

omit [Fact (1 < width)] [Fact (1 < height)] in
/-- The difference of the end pair and the right window is the left window. -/
theorem horizontalStaircaseEndPair_sdiff_rightWindow {L K : ℕ} (hxw : 2 * L ≤ width)
    (s : TorusVertex width height) :
    horizontalStaircaseEndPair s L K \ horizontalStaircaseRightWindow s L K =
      horizontalStaircaseLeftWindow s L K := by
  rw [horizontalStaircaseEndPair, Finset.union_sdiff_right,
    Finset.sdiff_eq_self_of_disjoint (horizontalStaircaseEndPair_disjoint hxw s)]

omit [Fact (1 < width)] [Fact (1 < height)] in
/-- **The complement of the left window splits into the right window and the rest.**

The torus complement of the left end window is the disjoint union of the right end window (the
window the bond `e` joins to) and the complement of the end pair `S`:
`univ \ W_0 = W_{L+K-1} ∪ (univ \ S)`.  Since `W_0 ⊆ S`, the host `univ \ W_0` is
`(S \ W_0) ∪ (univ \ S)`, and `S \ W_0 = W_{L+K-1}` at `2 * L ≤ width`.  This is the geometric
content of the bond-`e` contraction: pairing the left window against its complement reads the
opposite window's genuine block across `e` and the rest of the torus separately.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex` (the bond `e` joins the two windows);
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 4. -/
theorem compl_leftWindow_eq_rightWindow_union_complEndPair {L K : ℕ} (hxw : 2 * L ≤ width)
    (s : TorusVertex width height) :
    Finset.univ \ horizontalStaircaseLeftWindow s L K =
      horizontalStaircaseRightWindow s L K ∪
        (Finset.univ \ horizontalStaircaseEndPair s L K) := by
  rw [← horizontalStaircaseEndPair_sdiff_leftWindow hxw s, Finset.union_comm,
    Finset.sdiff_union_sdiff_cancel (Finset.subset_univ _)
      (horizontalStaircaseLeftWindow_subset_endPair s)]

omit [Fact (1 < width)] [Fact (1 < height)] in
/-- **The complement of the right window splits into the left window and the rest.**

The transpose of `compl_leftWindow_eq_rightWindow_union_complEndPair`:
`univ \ W_{L+K-1} = W_0 ∪ (univ \ S)`.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 4. -/
theorem compl_rightWindow_eq_leftWindow_union_complEndPair {L K : ℕ} (hxw : 2 * L ≤ width)
    (s : TorusVertex width height) :
    Finset.univ \ horizontalStaircaseRightWindow s L K =
      horizontalStaircaseLeftWindow s L K ∪
        (Finset.univ \ horizontalStaircaseEndPair s L K) := by
  rw [← horizontalStaircaseEndPair_sdiff_rightWindow hxw s, Finset.union_comm,
    Finset.sdiff_union_sdiff_cancel (Finset.subset_univ _)
      (horizontalStaircaseRightWindow_subset_endPair s)]

end Torus

end PEPS
end TNLean

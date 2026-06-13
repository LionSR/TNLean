import TNLean.PEPS.TorusWindowRegion

/-!
# Seam-wrapping window complements on the torus

The two-dimensional strengthening of the normal PEPS Fundamental Theorem
(arXiv:1804.04964, the corollary at lines 2297--2318 of
`Papers/1804.04964/paper_normal.tex`) inverts, around each lattice edge, the
torus complement of a single `L × K` window and of a consecutive-window union.
The filled-in derivation
(`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 1) records that each such
complement decomposes into a full-height band and one leftover rectangle, and
that the bands may wrap the torus seam.  This file supplies that geometry at the
minimal sizes `2L + 1 ≤ width`, `2K + 1 ≤ height`, where the wrapping is
unavoidable: the window occupies `L` (or `L + 1`) of the `2L + 1` columns, so the
remaining columns cannot split into two coordinate bands each at least `L` wide;
a single seam-wrapping band of `width - L ≥ L + 1` columns is forced.

The seam-wrapping rectangle is modelled by `torusArcRectangle`, the cyclic
product of two arcs read through `ZMod.val` cyclic distance.  A
wraparound-free arc rectangle coincides with the coordinate rectangle of
`TNLean/PEPS/TorusRectangleRegion.lean`
(`torusArcRectangle_eq_torusContiguousRectangle`), so the one-orientation window
hypotheses transport to arc rectangles unchanged.  The translation-invariant
hypothesis `NormalTorusArcWindowInjectivityHypotheses` asserts injectivity of
*every* cyclic `L × K` window, the form delivered by translation invariance of
the tensor; the wraparound-free `NormalTorusWindowInjectivityHypotheses` is its
seam-avoiding restriction.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964, the
  corollary and proof sketch at lines 2296--2445 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964);
  the filled-in derivation in
  `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`.
-/

namespace TNLean
namespace PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]

/-! ### Cyclic-distance arithmetic on `ZMod`

The arc computations reduce to natural-number arithmetic through the value of a
difference in `ZMod n`.  These are the `ZMod` counterparts of the `Fin`-valued
`val_sub_eq_ite` of `TNLean/PEPS/CycleArcRegion.lean`. -/

/-- The value of a difference in `ZMod n`: the plain difference when the
subtrahend value is not larger, and the wrapped difference otherwise. -/
theorem zmod_val_sub_eq_ite (n : ℕ) [NeZero n] (u v : ZMod n) :
    (u - v).val = if v.val ≤ u.val then u.val - v.val else u.val + n - v.val := by
  have hn : 0 < n := NeZero.pos n
  have hu := ZMod.val_lt u
  have hv := ZMod.val_lt v
  rw [sub_eq_add_neg, ZMod.val_add, ZMod.neg_val]
  by_cases hv0 : v = 0
  · have hvv : v.val = 0 := by rw [hv0, ZMod.val_zero]
    rw [if_pos hv0, hvv, if_pos (Nat.zero_le _)]
    simp only [Nat.sub_zero, Nat.add_zero]
    rw [Nat.mod_eq_of_lt hu]
  · rw [if_neg hv0]
    have hvval : 0 < v.val := by
      rcases Nat.eq_zero_or_pos v.val with h | h
      · exact absurd ((ZMod.val_eq_zero v).mp h) hv0
      · exact h
    split_ifs with h
    · rw [show u.val + (n - v.val) = (u.val - v.val) + n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    · rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- The cyclic distance from a start shifted by `L`: shifting the start of an arc
forward by `L` decreases the cyclic distance by `L`, wrapping when the original
distance is below `L`. -/
theorem zmod_val_sub_shift (n : ℕ) [NeZero n] (v s : ZMod n) (L : ℕ) (hL : L < n) :
    (v - (s + (L : ZMod n))).val =
      if (v - s).val < L then (v - s).val + n - L else (v - s).val - L := by
  rw [show v - (s + (L : ZMod n)) = (v - s) - (L : ZMod n) by ring, zmod_val_sub_eq_ite,
    ZMod.val_natCast, Nat.mod_eq_of_lt hL]
  have hd := ZMod.val_lt (v - s)
  split_ifs with h1 h2 h2 <;> omega

/-! ### The cyclic (seam-wrapping) torus rectangle -/

/-- A cyclic coordinate rectangle on the discrete torus: the vertices whose
cyclic distances from `s` lie below `xLen` and `yLen` respectively.  Unlike
`torusContiguousRectangle`, this rectangle may wrap the seam — it is read through
`ZMod.val` cyclic distance, so the columns `[s.1, s.1 + xLen)` are taken
cyclically.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex` (the complement bands that wrap the seam);
the filled-in derivation in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`. -/
def torusArcRectangle (s : TorusVertex width height) (xLen yLen : ℕ) :
    Finset (TorusVertex width height) :=
  Finset.univ.filter fun v => (v.1 - s.1).val < xLen ∧ (v.2 - s.2).val < yLen

@[simp] theorem mem_torusArcRectangle (s : TorusVertex width height) (xLen yLen : ℕ)
    (v : TorusVertex width height) :
    v ∈ torusArcRectangle s xLen yLen ↔
      (v.1 - s.1).val < xLen ∧ (v.2 - s.2).val < yLen := by
  simp [torusArcRectangle]

/-- A wraparound-free cyclic rectangle is the coordinate rectangle of
`TNLean/PEPS/TorusRectangleRegion.lean`: when the offsets and positive lengths
avoid the seam, the cyclic distances are the plain coordinate offsets.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1452 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem torusArcRectangle_eq_torusContiguousRectangle
    (xStart yStart xLen yLen : ℕ) (hxl : 0 < xLen) (hyl : 0 < yLen)
    (hx : xStart + xLen ≤ width) (hy : yStart + yLen ≤ height) :
    torusArcRectangle ((xStart : ZMod width), (yStart : ZMod height)) xLen yLen =
      torusContiguousRectangle xStart yStart xLen yLen := by
  ext v
  simp only [mem_torusArcRectangle, mem_torusContiguousRectangle]
  rw [zmod_val_sub_eq_ite width v.1 _, zmod_val_sub_eq_ite height v.2 _,
    ZMod.val_natCast_of_lt (show xStart < width by omega),
    ZMod.val_natCast_of_lt (show yStart < height by omega)]
  have hvx := ZMod.val_lt v.1
  have hvy := ZMod.val_lt v.2
  constructor
  · rintro ⟨h1, h2⟩
    split_ifs at h1 h2 <;> omega
  · rintro ⟨ha, hb, hc, hd⟩
    rw [if_pos (by omega), if_pos (by omega)]; omega

/-! ### Sliding-window tiling of a cyclic rectangle -/

/-- A cyclic rectangle of width at least `L` and height at least `K` (and not
exceeding the torus dimensions) is the union of the cyclic `L × K` windows
sliding over it.  This is the seam-wrapping counterpart of
`contiguousRectangle_eq_biUnion_window`.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1322--1430 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem torusArcRectangle_eq_biUnion_window {L K : ℕ} (hL : 0 < L) (hK : 0 < K)
    (s : TorusVertex width height) (xLen yLen : ℕ)
    (hx : L ≤ xLen) (hy : K ≤ yLen) (hxw : xLen ≤ width) (hyh : yLen ≤ height) :
    torusArcRectangle s xLen yLen =
      (Finset.range (xLen - L + 1) ×ˢ Finset.range (yLen - K + 1)).biUnion
        (fun p => torusArcRectangle
          (s.1 + (p.1 : ZMod width), s.2 + (p.2 : ZMod height)) L K) := by
  ext v
  simp only [mem_torusArcRectangle, Finset.mem_biUnion, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨hvx, hvy⟩
    refine ⟨(min ((v.1 - s.1).val) (xLen - L), min ((v.2 - s.2).val) (yLen - K)),
      ⟨by omega, by omega⟩, ?_⟩
    rw [zmod_val_sub_shift width v.1 s.1 _ (by omega),
      zmod_val_sub_shift height v.2 s.2 _ (by omega)]
    refine ⟨?_, ?_⟩
    · split_ifs with hc <;> omega
    · split_ifs with hc <;> omega
  · rintro ⟨⟨p, q⟩, ⟨hp, hq⟩, hvx, hvy⟩
    rw [zmod_val_sub_shift width v.1 s.1 _ (by omega)] at hvx
    rw [zmod_val_sub_shift height v.2 s.2 _ (by omega)] at hvy
    refine ⟨?_, ?_⟩
    · split_ifs at hvx with hc <;> omega
    · split_ifs at hvy with hc <;> omega

/-! ### The translation-invariant one-orientation window hypotheses

The wraparound-free hypotheses `NormalTorusWindowInjectivityHypotheses` cover
only coordinate windows clear of the seam.  Translation invariance of the
tensor makes *every* cyclic `L × K` window injective, including the seam-wrapping
ones the complement bands require; that is recorded here. -/

/-- The translation-invariant one-orientation window-injectivity hypotheses: every
cyclic `L × K` window is injective, including the seam-wrapping ones.  This is the
form delivered by translation invariance of the tensor, and the form the
seam-wrapping complement bands consume.

Source: arXiv:1804.04964, the corollary at lines 2297--2318 of
`Papers/1804.04964/paper_normal.tex` ("every $L \times K$ region is injective",
read translation-invariantly); scoped in
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`. -/
structure NormalTorusArcWindowInjectivityHypotheses (L K : ℕ)
    (κ : RegionInjectivityData (TorusVertex width height)) where
  /-- Every cyclic `L × K` window is injective. -/
  arcWindow_injective :
    ∀ s : TorusVertex width height, κ.IsInjective (torusArcRectangle s L K)

namespace NormalTorusArcWindowInjectivityHypotheses

variable {L K : ℕ} {κ : RegionInjectivityData (TorusVertex width height)}

/-- The translation-invariant hypotheses restrict to the seam-avoiding window
hypotheses: every wraparound-free coordinate `L × K` window is injective.

Source: arXiv:1804.04964, the corollary at lines 2297--2318 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem toWindowHypotheses (h : NormalTorusArcWindowInjectivityHypotheses L K κ)
    (hL : 0 < L) (hK : 0 < K) :
    NormalTorusWindowInjectivityHypotheses L K κ where
  window_injective xStart yStart hx hy := by
    rw [← torusArcRectangle_eq_torusContiguousRectangle xStart yStart L K hL hK hx hy]
    exact h.arcWindow_injective _

/-- A cyclic rectangle of width at least `L` and height at least `K` is injective
under the translation-invariant window hypotheses: it is the union of the cyclic
`L × K` windows sliding over it.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union` and the corollary at
lines 2297--2318 of `Papers/1804.04964/paper_normal.tex`. -/
theorem arcRectangle_injective (h : NormalTorusArcWindowInjectivityHypotheses L K κ)
    (hUnion : RegionInjectivityUnionClosure κ) (hL : 0 < L) (hK : 0 < K)
    {s : TorusVertex width height} {xLen yLen : ℕ}
    (hx : L ≤ xLen) (hy : K ≤ yLen) (hxw : xLen ≤ width) (hyh : yLen ≤ height) :
    κ.IsInjective (torusArcRectangle s xLen yLen) := by
  rw [torusArcRectangle_eq_biUnion_window hL hK s xLen yLen hx hy hxw hyh]
  refine hUnion.biUnion_injective ?_ _ ?_
  · exact ⟨(0, 0), by simp [Finset.mem_product, Finset.mem_range]⟩
  · rintro ⟨p, q⟩ _
    exact h.arcWindow_injective _

end NormalTorusArcWindowInjectivityHypotheses

/-! ### Consecutive-window unions

The overlapping-window chain compares consecutive windows.  Two horizontally
consecutive windows of the chain are `L × K` cyclic rectangles offset by one
column; their union is the single `(L + 1) × K` cyclic rectangle of the chain's
horizontal slide.  Two vertically consecutive windows are offset by one row and
union to the `L × (K + 1)` rectangle of the vertical descent.  Each union is a
single cyclic rectangle of width at least `L` and height at least `K`, hence
injective by the sliding-window tiling. -/

/-- The union of two horizontally consecutive windows (offset by one column) is
the single `(L + 1) × K` cyclic rectangle.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex` (the consecutive-window union is an
$(L+1)\times K$ rectangle); `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 1. -/
theorem horizontalAdjacentWindows_union {L K : ℕ} (hL : 0 < L) (hw : 1 < width)
    (s : TorusVertex width height) :
    torusArcRectangle s L K ∪ torusArcRectangle (s.1 + (1 : ZMod width), s.2) L K =
      torusArcRectangle s (L + 1) K := by
  ext v
  simp only [mem_torusArcRectangle, Finset.mem_union]
  rw [show (1 : ZMod width) = ((1 : ℕ) : ZMod width) by norm_cast,
    zmod_val_sub_shift width v.1 s.1 1 hw]
  have hx := ZMod.val_lt (v.1 - s.1)
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨by omega, h2⟩
    · refine ⟨?_, h2⟩
      split_ifs at h1 with hc <;> omega
  · rintro ⟨h1, h2⟩
    by_cases hc : (v.1 - s.1).val < L
    · exact Or.inl ⟨hc, h2⟩
    · refine Or.inr ⟨?_, h2⟩
      rw [if_neg (by omega : ¬ (v.1 - s.1).val < 1)]; omega

/-- The union of two vertically consecutive windows (offset by one row) is the
single `L × (K + 1)` cyclic rectangle.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex` (the vertical-slide union is an
$L\times(K+1)$ rectangle); `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 1. -/
theorem verticalAdjacentWindows_union {L K : ℕ} (hK : 0 < K) (hh : 1 < height)
    (s : TorusVertex width height) :
    torusArcRectangle s L K ∪ torusArcRectangle (s.1, s.2 + (1 : ZMod height)) L K =
      torusArcRectangle s L (K + 1) := by
  ext v
  simp only [mem_torusArcRectangle, Finset.mem_union]
  rw [show (1 : ZMod height) = ((1 : ℕ) : ZMod height) by norm_cast,
    zmod_val_sub_shift height v.2 s.2 1 hh]
  have hy := ZMod.val_lt (v.2 - s.2)
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨h1, by omega⟩
    · refine ⟨h1, ?_⟩
      split_ifs at h2 with hc <;> omega
  · rintro ⟨h1, h2⟩
    by_cases hc : (v.2 - s.2).val < K
    · exact Or.inl ⟨h1, hc⟩
    · refine Or.inr ⟨h1, ?_⟩
      rw [if_neg (by omega : ¬ (v.2 - s.2).val < 1)]; omega

namespace NormalTorusArcWindowInjectivityHypotheses

variable {L K : ℕ} {κ : RegionInjectivityData (TorusVertex width height)}

/-- A horizontally consecutive-window union is injective: it is the
`(L + 1) × K` cyclic rectangle, a width-at-least-`L`, height-at-least-`K`
rectangle.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 1. -/
theorem horizontalUnion_injective (h : NormalTorusArcWindowInjectivityHypotheses L K κ)
    (hUnion : RegionInjectivityUnionClosure κ) (hL : 2 ≤ L) (hK : 2 ≤ K)
    (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height) (s : TorusVertex width height) :
    κ.IsInjective (torusArcRectangle s (L + 1) K) :=
  h.arcRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)

/-- A vertically consecutive-window union is injective: it is the `L × (K + 1)`
cyclic rectangle.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 1. -/
theorem verticalUnion_injective (h : NormalTorusArcWindowInjectivityHypotheses L K κ)
    (hUnion : RegionInjectivityUnionClosure κ) (hL : 2 ≤ L) (hK : 2 ≤ K)
    (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height) (s : TorusVertex width height) :
    κ.IsInjective (torusArcRectangle s L (K + 1)) :=
  h.arcRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)

end NormalTorusArcWindowInjectivityHypotheses

/-! ### The two-piece complement of a cyclic rectangle

The torus complement of a cyclic rectangle of width `w < width` and height
`h < height` is the union of two cyclic rectangles: a full-height band of the
`width - w` columns outside it, and the `w`-column band of the `height - h` rows
outside it.  The first band starts where the rectangle's columns end and wraps
the seam; the second sits in the rectangle's columns above its rows. -/

/-- **The two-piece complement of a cyclic torus rectangle.**

For a cyclic rectangle of width `w < width` and height `h < height`, the torus
complement is the union of a full-height band of `width - w` columns (starting
where the rectangle ends, wrapping the seam) and a `w`-column band of
`height - h` rows (above the rectangle).  This is the filled-in derivation's
"full-height band ... and a leftover rectangle"
(`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 1).

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem compl_torusArcRectangle (s : TorusVertex width height) (w h : ℕ)
    (hw : w < width) (hh : h < height) :
    (Finset.univ \ torusArcRectangle s w h : Finset (TorusVertex width height)) =
      torusArcRectangle (s.1 + (w : ZMod width), s.2) (width - w) height ∪
        torusArcRectangle (s.1, s.2 + (h : ZMod height)) w (height - h) := by
  ext v
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, mem_torusArcRectangle,
    Finset.mem_union, not_and, not_lt]
  have hx := ZMod.val_lt (v.1 - s.1)
  have hy := ZMod.val_lt (v.2 - s.2)
  have hsx := zmod_val_sub_shift width v.1 s.1 w hw
  have hsy := zmod_val_sub_shift height v.2 s.2 h hh
  constructor
  · intro hv
    by_cases hxin : (v.1 - s.1).val < w
    · refine Or.inr ⟨hxin, ?_⟩
      have hyout : h ≤ (v.2 - s.2).val := hv hxin
      rw [hsy, if_neg (by omega)]; omega
    · refine Or.inl ⟨?_, hy⟩
      rw [hsx, if_neg hxin]; omega
  · rintro (⟨hxb, _⟩ | ⟨hxin, hyb⟩) hxin'
    · rw [hsx, if_pos hxin'] at hxb; omega
    · rw [hsy] at hyb
      split_ifs at hyb with hyin <;> omega

namespace NormalTorusArcWindowInjectivityHypotheses

variable {L K : ℕ} {κ : RegionInjectivityData (TorusVertex width height)}

/-- **The complement of a single window decomposes into two injective bands.**

At the minimal sizes `2L + 1 ≤ width`, `2K + 1 ≤ height`, the torus complement
of a cyclic `L × K` window is injective: it is the union of a full-height band of
`width - L ≥ L + 1` columns and an `L`-column band of `height - K ≥ K + 1` rows,
each a cyclic rectangle of width at least `L` and height at least `K`.  The
full-height band wraps the seam, which is unavoidable at these sizes since the
window occupies `L` of only `2L + 1` columns.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex`; the derivation in
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 1. -/
theorem windowComplement_injective (h : NormalTorusArcWindowInjectivityHypotheses L K κ)
    (hUnion : RegionInjectivityUnionClosure κ) (hL : 2 ≤ L) (hK : 2 ≤ K)
    (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height) (s : TorusVertex width height) :
    κ.IsInjective (Finset.univ \ torusArcRectangle s L K) := by
  rw [compl_torusArcRectangle s L K (by omega) (by omega)]
  refine hUnion.union_injective ?_ ?_
  · exact h.arcRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
  · exact h.arcRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)

/-- **The complement of a consecutive-window union decomposes into two injective
bands.**

The union of two consecutive windows of the overlapping-window chain is a cyclic
`(L + 1) × K` rectangle (a horizontal slide).  At the minimal sizes its torus
complement is injective: it is the union of a full-height band of
`width - L - 1 ≥ L` columns and an `(L + 1)`-column band of `height - K ≥ K`
rows.  This is the only step of the argument where the torus size enters, matching
the source's parenthetical "$(2L+1)\times(2K+1)$".

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex`; the derivation in
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 1. -/
theorem horizontalUnionComplement_injective
    (h : NormalTorusArcWindowInjectivityHypotheses L K κ)
    (hUnion : RegionInjectivityUnionClosure κ) (hL : 2 ≤ L) (hK : 2 ≤ K)
    (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height) (s : TorusVertex width height) :
    κ.IsInjective (Finset.univ \ torusArcRectangle s (L + 1) K) := by
  rw [compl_torusArcRectangle s (L + 1) K (by omega) (by omega)]
  refine hUnion.union_injective ?_ ?_
  · exact h.arcRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
  · exact h.arcRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)

/-- **The complement of a vertically consecutive-window union decomposes into two
injective bands.**

The transposed counterpart of `horizontalUnionComplement_injective`: the union of
two vertically consecutive windows is a cyclic `L × (K + 1)` rectangle (a vertical
slide), and at the minimal sizes its torus complement is the union of a
full-height band of `width - L ≥ L + 1` columns and an `L`-column band of
`height - K - 1 ≥ K` rows.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex`; the derivation in
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 1. -/
theorem verticalUnionComplement_injective
    (h : NormalTorusArcWindowInjectivityHypotheses L K κ)
    (hUnion : RegionInjectivityUnionClosure κ) (hL : 2 ≤ L) (hK : 2 ≤ K)
    (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height) (s : TorusVertex width height) :
    κ.IsInjective (Finset.univ \ torusArcRectangle s L (K + 1)) := by
  rw [compl_torusArcRectangle s L (K + 1) (by omega) (by omega)]
  refine hUnion.union_injective ?_ ?_
  · exact h.arcRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
  · exact h.arcRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)

end NormalTorusArcWindowInjectivityHypotheses

end PEPS
end TNLean

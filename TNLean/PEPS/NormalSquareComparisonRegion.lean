import TNLean.PEPS.NormalEdgeBlockingInterior
import TNLean.PEPS.RegionBlock.Basic

/-!
# The comparison region of the open-lattice normal PEPS Fundamental Theorem

The final comparison of the normal PEPS Fundamental Theorem runs over a region `R` and the
one-site-larger region `S = R ∪ {v}` (arXiv:1804.04964, Section 3, proof of Theorem 3, lines
1519--1571 of `Papers/1804.04964/paper_normal.tex`).  This file builds that pair on the finite
open square lattice at a parametric offset `(a, b)`: the **comparison region** is the `3 × 3`
coordinate square at `(a, b)` minus its lower-left corner, so that

* the comparison region is the union of a `2 × 3` and a `3 × 2` source rectangle, hence
  injective;
* inserting the corner vertex completes the square, a `3 × 3` rectangle, hence injective;
* both complements decompose into coordinate bands (and one corner rectangle), all of source
  shape, hence injective by union closure (the source's "if the PEPS is at least `5 × 5`, their
  complement regions are also injective", line 1543);
* both regions have a boundary edge; and
* with the offset in the **interior window** (`4 ≤ a`, `a + 9 ≤ width`, `4 ≤ b`,
  `b + 9 ≤ height`), every boundary edge of both regions carries the interior margins of the
  open edge-blocking geometry, so the bare-edge absorbed equality of the interior gauge family
  is available on all of them.

Unlike the torus, where one reference pair is transported to every site by the translations, the
open lattice carries no translations, so the pair is placed afresh at every offset; the interior
window is the set of offsets the open blocking geometry reaches.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1571
  of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

namespace TNLean
namespace PEPS

variable {width height : ℕ}

/-! ### The comparison square, comparison region, and interior window -/

/-- The `3 × 3` coordinate square at offset `(a, b)`. -/
def normalSquareComparisonSquare (a b : ℕ) : Finset (SquareLatticeVertex width height) :=
  squareLatticeContiguousRectangle a b 3 3

/-- The comparison region: the `3 × 3` square at `(a, b)` minus its lower-left corner,
presented as the union of a `2 × 3` rectangle and a `3 × 2` rectangle.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1544 of
`Papers/1804.04964/paper_normal.tex` (the displayed regions `R` and `S`). -/
def normalSquareComparisonRegion (a b : ℕ) : Finset (SquareLatticeVertex width height) :=
  squareLatticeContiguousRectangle (a + 1) b 2 3 ∪
    squareLatticeContiguousRectangle a (b + 1) 3 2

/-- The interior window for the comparison offset: the placement margins under which every
boundary edge of the comparison square and the comparison region carries the interior margins of
the open edge-blocking geometry.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1571 of
`Papers/1804.04964/paper_normal.tex`; the window records which offsets the open-lattice blocking
frames reach. -/
def IsNormalSquareComparisonWindow (width height a b : ℕ) : Prop :=
  4 ≤ a ∧ a + 9 ≤ width ∧ 4 ≤ b ∧ b + 9 ≤ height

/-- Membership in the comparison region, in coordinate values. -/
theorem mem_normalSquareComparisonRegion (a b : ℕ) (v : SquareLatticeVertex width height) :
    v ∈ (normalSquareComparisonRegion a b : Finset (SquareLatticeVertex width height)) ↔
      (a + 1 ≤ v.1.1 ∧ v.1.1 < a + 3 ∧ b ≤ v.2.1 ∧ v.2.1 < b + 3) ∨
        (a ≤ v.1.1 ∧ v.1.1 < a + 3 ∧ b + 1 ≤ v.2.1 ∧ v.2.1 < b + 3) := by
  simp only [normalSquareComparisonRegion, Finset.mem_union,
    mem_squareLatticeContiguousRectangle]

/-- A vertex lies outside the comparison region at its own coordinates. -/
theorem notMem_normalSquareComparisonRegion (v : SquareLatticeVertex width height) :
    v ∉ (normalSquareComparisonRegion v.1.1 v.2.1 :
      Finset (SquareLatticeVertex width height)) := by
  rw [mem_normalSquareComparisonRegion]
  omega

/-- Inserting the corner vertex into the comparison region completes the comparison square. -/
theorem insert_normalSquareComparisonRegion (v : SquareLatticeVertex width height) :
    insert v (normalSquareComparisonRegion v.1.1 v.2.1) =
      (normalSquareComparisonSquare v.1.1 v.2.1 :
        Finset (SquareLatticeVertex width height)) := by
  ext w
  rw [Finset.mem_insert, mem_normalSquareComparisonRegion, normalSquareComparisonSquare,
    mem_squareLatticeContiguousRectangle]
  constructor
  · rintro (rfl | hw)
    · exact ⟨by omega, by omega, by omega, by omega⟩
    · omega
  · rintro ⟨h1, h2, h3, h4⟩
    by_cases hw : w = v
    · exact Or.inl hw
    · refine Or.inr ?_
      have hne : w.1.1 ≠ v.1.1 ∨ w.2.1 ≠ v.2.1 := by
        by_contra hcon
        push Not at hcon
        exact hw (Prod.ext (Fin.ext hcon.1) (Fin.ext hcon.2))
      omega

/-! ### The band decompositions of the complements -/

/-- The complement of the comparison square is the union of four coordinate bands. -/
theorem compl_normalSquareComparisonSquare_eq_bands {a b : ℕ}
    (ha : a + 3 ≤ width) (hb : b + 3 ≤ height) :
    Finset.univ \
        (normalSquareComparisonSquare a b : Finset (SquareLatticeVertex width height)) =
      squareLatticeContiguousRectangle 0 0 a height ∪
        (squareLatticeContiguousRectangle (a + 3) 0 (width - (a + 3)) height ∪
          (squareLatticeContiguousRectangle a 0 3 b ∪
            squareLatticeContiguousRectangle a (b + 3) 3 (height - (b + 3)))) := by
  ext v
  have hx := v.1.isLt
  have hy := v.2.isLt
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union,
    normalSquareComparisonSquare, mem_squareLatticeContiguousRectangle]
  omega

/-- The complement of the comparison region is the union of the four bands and the corner
rectangle covering the corner vertex. -/
theorem compl_normalSquareComparisonRegion_eq_bands {a b : ℕ}
    (ha2 : 2 ≤ a) (hb1 : 1 ≤ b) (ha : a + 3 ≤ width) (hb : b + 3 ≤ height) :
    Finset.univ \
        (normalSquareComparisonRegion a b : Finset (SquareLatticeVertex width height)) =
      squareLatticeContiguousRectangle (a - 2) (b - 1) 3 2 ∪
        (squareLatticeContiguousRectangle 0 0 a height ∪
          (squareLatticeContiguousRectangle (a + 3) 0 (width - (a + 3)) height ∪
            (squareLatticeContiguousRectangle a 0 3 b ∪
              squareLatticeContiguousRectangle a (b + 3) 3 (height - (b + 3))))) := by
  ext v
  have hx := v.1.isLt
  have hy := v.2.isLt
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union,
    mem_normalSquareComparisonRegion, mem_squareLatticeContiguousRectangle]
  omega

/-! ### Injectivity of the comparison regions and their complements -/

namespace NormalSquareLatticeRectangleInjectivityHypotheses

variable {κ : RegionInjectivityData (SquareLatticeVertex width height)}

/-- The comparison region is injective: it is the union of a `2 × 3` and a `3 × 2` source
rectangle.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union` and proof of Theorem 3, lines
1322--1544 of `Papers/1804.04964/paper_normal.tex`. -/
theorem comparisonRegion_injective (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ) {a b : ℕ}
    (ha : a + 3 ≤ width) (hb : b + 3 ≤ height) :
    κ.IsInjective
      (normalSquareComparisonRegion a b : Finset (SquareLatticeVertex width height)) :=
  hUnion.union_injective (h.rect23_injective (by omega) (by omega))
    (h.rect32_injective (by omega) (by omega))

/-- The comparison square is injective: it is a `3 × 3` rectangle.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union` and proof of Theorem 3, lines
1322--1544 of `Papers/1804.04964/paper_normal.tex`. -/
theorem comparisonSquare_injective (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ) {a b : ℕ}
    (ha : a + 3 ≤ width) (hb : b + 3 ≤ height) :
    κ.IsInjective
      (normalSquareComparisonSquare a b : Finset (SquareLatticeVertex width height)) :=
  h.wideRectangle_injective hUnion (by omega) (by omega) ha hb

/-- The complement of the comparison square is injective: it is the union of four coordinate
bands, each of source shape.  These are the placement margins of the source's "if the PEPS is at
least `5 × 5`, their complement regions `R^c` and `S^c` are also injective" (line 1543).

Source: arXiv:1804.04964, Section 3, Lemma `injective_union` and proof of Theorem 3, lines
1322--1544 of `Papers/1804.04964/paper_normal.tex`. -/
theorem compl_comparisonSquare_injective
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ) {a b : ℕ}
    (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (ha : a + 5 ≤ width) (hb : b + 5 ≤ height) :
    κ.IsInjective (Finset.univ \
      (normalSquareComparisonSquare a b : Finset (SquareLatticeVertex width height))) := by
  rw [compl_normalSquareComparisonSquare_eq_bands (by omega) (by omega)]
  refine hUnion.union_injective
    (h.wideRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega)) ?_
  refine hUnion.union_injective
    (h.wideRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega)) ?_
  exact hUnion.union_injective
    (h.shortRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega))
    (h.shortRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega))

/-- The complement of the comparison region is injective: it is the union of the four bands and
a `3 × 2` corner rectangle.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union` and proof of Theorem 3, lines
1322--1544 of `Papers/1804.04964/paper_normal.tex`. -/
theorem compl_comparisonRegion_injective
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ) {a b : ℕ}
    (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (ha : a + 5 ≤ width) (hb : b + 5 ≤ height) :
    κ.IsInjective (Finset.univ \
      (normalSquareComparisonRegion a b : Finset (SquareLatticeVertex width height))) := by
  rw [compl_normalSquareComparisonRegion_eq_bands (by omega) (by omega) (by omega) (by omega)]
  refine hUnion.union_injective
    (h.shortRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega)) ?_
  refine hUnion.union_injective
    (h.wideRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega)) ?_
  refine hUnion.union_injective
    (h.wideRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega)) ?_
  exact hUnion.union_injective
    (h.shortRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega))
    (h.shortRectangle_injective hUnion (by omega) (by omega) (by omega) (by omega))

end NormalSquareLatticeRectangleInjectivityHypotheses

/-! ### Boundary edges of the comparison regions -/

/-- The up edge of the corner vertex is a boundary edge of the comparison region: the corner
`(a, b)` lies outside, its upper neighbour `(a, b + 1)` inside. -/
theorem isRegionBoundaryEdge_normalSquareComparisonRegion {a b : ℕ}
    (ha : a < width) (hb : b + 2 < height) :
    IsRegionBoundaryEdge (G := squareLatticeGraph width height)
      (normalSquareComparisonRegion a b)
      (squareLatticeUpEdge a b ha (by omega)) := by
  refine Or.inr ⟨?_, ?_⟩
  · rw [mem_normalSquareComparisonRegion]
    simp only [squareLatticeUpEdge]
    omega
  · rw [mem_normalSquareComparisonRegion]
    simp only [squareLatticeUpEdge]
    omega

/-- The up edge of the vertex below the corner is a boundary edge of the comparison square:
`(a, b - 1)` lies outside, its upper neighbour `(a, b)` inside. -/
theorem isRegionBoundaryEdge_normalSquareComparisonSquare {a b : ℕ}
    (hb1 : 1 ≤ b) (ha : a < width) (hb : b + 2 < height) :
    IsRegionBoundaryEdge (G := squareLatticeGraph width height)
      (normalSquareComparisonSquare a b)
      (squareLatticeUpEdge a (b - 1) ha (by omega)) := by
  refine Or.inr ⟨?_, ?_⟩
  · rw [normalSquareComparisonSquare, mem_squareLatticeContiguousRectangle]
    simp only [squareLatticeUpEdge]
    omega
  · rw [normalSquareComparisonSquare, mem_squareLatticeContiguousRectangle]
    simp only [squareLatticeUpEdge]
    omega

/-! ### Boundary edges of the comparison regions are interior edges

With the offset in the interior window, every boundary edge of the comparison square and the
comparison region carries the interior margins of the open edge-blocking geometry, so the
bare-edge absorbed equality of the interior gauge family is available on all of them. -/

/-- Every boundary edge of the comparison square at a window offset is an interior edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1571 of
`Papers/1804.04964/paper_normal.tex`; the open-lattice placement margins. -/
theorem normalSquareInteriorEdgeDatum_of_boundary_comparisonSquare {a b : ℕ}
    (hwin : IsNormalSquareComparisonWindow width height a b)
    {f : Edge (squareLatticeGraph width height)}
    (hf : IsRegionBoundaryEdge (G := squareLatticeGraph width height)
      (normalSquareComparisonSquare a b) f) :
    NormalSquareInteriorEdgeDatum f := by
  obtain ⟨ha4, haw, hb4, hbh⟩ := hwin
  rcases squareLatticeEdge_horizontal_or_vertical f with hH | hV
  · have hc := horizontalSquareLatticeEdge_coords f hH
    have hy2 : f.1.2.2.1 = f.1.1.2.1 := (congrArg Fin.val hc.1).symm
    have hx2 : f.1.2.1.1 = f.1.1.1.1 + 1 := hc.2.symm
    refine NormalSquareInteriorEdgeDatum.horizontal hH ⟨?_, ?_, ?_, ?_⟩ <;>
      (rcases hf with ⟨hin, hout⟩ | ⟨hout, hin⟩ <;>
        simp only [normalSquareComparisonSquare,
          mem_squareLatticeContiguousRectangle] at hin hout <;>
        omega)
  · have hc := verticalSquareLatticeEdge_coords f hV
    have hx2 : f.1.2.1.1 = f.1.1.1.1 := (congrArg Fin.val hc.1).symm
    have hy2 : f.1.2.2.1 = f.1.1.2.1 + 1 := hc.2.symm
    refine NormalSquareInteriorEdgeDatum.vertical hV ⟨?_, ?_, ?_, ?_⟩ <;>
      (rcases hf with ⟨hin, hout⟩ | ⟨hout, hin⟩ <;>
        simp only [normalSquareComparisonSquare,
          mem_squareLatticeContiguousRectangle] at hin hout <;>
        omega)

/-- Every boundary edge of the comparison region at a window offset is an interior edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1571 of
`Papers/1804.04964/paper_normal.tex`; the open-lattice placement margins. -/
theorem normalSquareInteriorEdgeDatum_of_boundary_comparisonRegion {a b : ℕ}
    (hwin : IsNormalSquareComparisonWindow width height a b)
    {f : Edge (squareLatticeGraph width height)}
    (hf : IsRegionBoundaryEdge (G := squareLatticeGraph width height)
      (normalSquareComparisonRegion a b) f) :
    NormalSquareInteriorEdgeDatum f := by
  obtain ⟨ha4, haw, hb4, hbh⟩ := hwin
  rcases squareLatticeEdge_horizontal_or_vertical f with hH | hV
  · have hc := horizontalSquareLatticeEdge_coords f hH
    have hy2 : f.1.2.2.1 = f.1.1.2.1 := (congrArg Fin.val hc.1).symm
    have hx2 : f.1.2.1.1 = f.1.1.1.1 + 1 := hc.2.symm
    refine NormalSquareInteriorEdgeDatum.horizontal hH ⟨?_, ?_, ?_, ?_⟩ <;>
      (rcases hf with ⟨hin, hout⟩ | ⟨hout, hin⟩ <;>
        rw [mem_normalSquareComparisonRegion] at hin hout <;>
        omega)
  · have hc := verticalSquareLatticeEdge_coords f hV
    have hx2 : f.1.2.1.1 = f.1.1.1.1 := (congrArg Fin.val hc.1).symm
    have hy2 : f.1.2.2.1 = f.1.1.2.1 + 1 := hc.2.symm
    refine NormalSquareInteriorEdgeDatum.vertical hV ⟨?_, ?_, ?_, ?_⟩ <;>
      (rcases hf with ⟨hin, hout⟩ | ⟨hout, hin⟩ <;>
        rw [mem_normalSquareComparisonRegion] at hin hout <;>
        omega)

end PEPS
end TNLean

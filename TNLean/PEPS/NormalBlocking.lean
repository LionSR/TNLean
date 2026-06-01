import Mathlib.Data.Finset.Prod

import TNLean.PEPS.NormalEdgeBlockingData

/-!
# Normal PEPS blocking hypotheses

The normal PEPS proof in arXiv:1804.04964 first blocks the lattice into
injective regions, then applies the same three-site injective-chain argument
used for injective PEPS.  We record the finite-region hypotheses
needed for that reduction.

The hypotheses below do not prove that a given geometric square-lattice region
is injective.  Instead they make explicit the assumptions carried by the normal
theorem: local rectangular injectivity, edge-centred three-region blockings, and
one-site-different injective regions with injective complements.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, Theorem 3 and Theorem normal](https://arxiv.org/abs/1804.04964)
-/

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

variable (ι : RegionInjectivityData V)

/-! ### Coordinate regions for the square-lattice normal theorem -/

/-- The vertex type of a finite rectangular square lattice of size
`width × height`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1452 of
`Papers/1804.04964/paper_normal.tex`, where the normal theorem is specialized
to finite square lattices. -/
abbrev SquareLatticeVertex (width height : ℕ) :=
  Fin width × Fin height

/-- A coordinate rectangle in a finite square lattice, specified by its
horizontal and vertical coordinate sets.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1452 of
`Papers/1804.04964/paper_normal.tex`, where the regions \(R\), \(S\), and
\(T\) are assembled from rectangular \(2\times3\) and \(3\times2\) blocks. -/
def squareLatticeRectangle {width height : ℕ}
    (xs : Finset (Fin width)) (ys : Finset (Fin height)) :
    Finset (SquareLatticeVertex width height) :=
  xs ×ˢ ys

@[simp] theorem mem_squareLatticeRectangle {width height : ℕ}
    (xs : Finset (Fin width)) (ys : Finset (Fin height))
    (v : SquareLatticeVertex width height) :
    v ∈ squareLatticeRectangle xs ys ↔ v.1 ∈ xs ∧ v.2 ∈ ys := by
  simp [squareLatticeRectangle]

@[simp] theorem card_squareLatticeRectangle {width height : ℕ}
    (xs : Finset (Fin width)) (ys : Finset (Fin height)) :
    (squareLatticeRectangle xs ys).card = xs.card * ys.card := by
  simp [squareLatticeRectangle]

/-- The full finite rectangular square lattice as a coordinate region.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1452 of
`Papers/1804.04964/paper_normal.tex`, where the argument uses a finite
rectangular square lattice as the ambient region. -/
def squareLatticeFull (width height : ℕ) : Finset (SquareLatticeVertex width height) :=
  squareLatticeRectangle Finset.univ Finset.univ

@[simp] theorem squareLatticeFull_eq_univ (width height : ℕ) :
    squareLatticeFull width height = Finset.univ := by
  ext v
  simp [squareLatticeFull]

/-- A contiguous interval of coordinates in one axis of a finite square lattice.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1452 of
`Papers/1804.04964/paper_normal.tex`, where the normal square-lattice theorem
uses contiguous \(2\times3\) and \(3\times2\) rectangular blocks. -/
def squareLatticeCoordinateInterval {size : ℕ} (start length : ℕ) : Finset (Fin size) :=
  Finset.univ.filter fun i ↦ start ≤ i.1 ∧ i.1 < start + length

@[simp] theorem mem_squareLatticeCoordinateInterval {size : ℕ}
    (start length : ℕ) (i : Fin size) :
    i ∈ squareLatticeCoordinateInterval start length ↔
      start ≤ i.1 ∧ i.1 < start + length := by
  simp [squareLatticeCoordinateInterval]

/-- A contiguous coordinate rectangle in a finite square lattice.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1452 of
`Papers/1804.04964/paper_normal.tex`, where the regions \(R\), \(S\), and
\(T\) are assembled from contiguous \(2\times3\) and \(3\times2\) rectangles. -/
def squareLatticeContiguousRectangle {width height : ℕ}
    (xStart yStart xLength yLength : ℕ) :
    Finset (SquareLatticeVertex width height) :=
  squareLatticeRectangle
    (squareLatticeCoordinateInterval xStart xLength)
    (squareLatticeCoordinateInterval yStart yLength)

@[simp] theorem mem_squareLatticeContiguousRectangle {width height : ℕ}
    (xStart yStart xLength yLength : ℕ)
    (v : SquareLatticeVertex width height) :
    v ∈ squareLatticeContiguousRectangle xStart yStart xLength yLength ↔
      xStart ≤ v.1.1 ∧ v.1.1 < xStart + xLength ∧
        yStart ≤ v.2.1 ∧ v.2.1 < yStart + yLength := by
  simp [squareLatticeContiguousRectangle, and_assoc]

/-- Coordinate-product regions with two horizontal and three vertical
coordinates.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1452 of
`Papers/1804.04964/paper_normal.tex`. This is preliminary coordinate
vocabulary for the \(2\times3\) rectangles appearing there, not yet the
source-paper contiguous-block notion. -/
def IsTwoByThreeSquareLatticeProduct {width height : ℕ}
    (R : Finset (SquareLatticeVertex width height)) : Prop :=
  ∃ xs : Finset (Fin width), ∃ ys : Finset (Fin height),
    xs.card = 2 ∧ ys.card = 3 ∧ R = squareLatticeRectangle xs ys

/-- Coordinate-product regions with three horizontal and two vertical
coordinates.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1452 of
`Papers/1804.04964/paper_normal.tex`. This is preliminary coordinate
vocabulary for the \(3\times2\) rectangles appearing there, not yet the
source-paper contiguous-block notion. -/
def IsThreeByTwoSquareLatticeProduct {width height : ℕ}
    (R : Finset (SquareLatticeVertex width height)) : Prop :=
  ∃ xs : Finset (Fin width), ∃ ys : Finset (Fin height),
    xs.card = 3 ∧ ys.card = 2 ∧ R = squareLatticeRectangle xs ys

/-- Contiguous coordinate rectangles of width two and height three.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1452 of
`Papers/1804.04964/paper_normal.tex`, where the normal square-lattice theorem
assumes injectivity for contiguous \(2\times3\) rectangular blocks. -/
def IsTwoByThreeContiguousSquareLatticeRectangle {width height : ℕ}
    (R : Finset (SquareLatticeVertex width height)) : Prop :=
  ∃ xStart yStart : ℕ,
    xStart + 2 ≤ width ∧ yStart + 3 ≤ height ∧
      R = squareLatticeContiguousRectangle xStart yStart 2 3

/-- Contiguous coordinate rectangles of width three and height two.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1452 of
`Papers/1804.04964/paper_normal.tex`, where the normal square-lattice theorem
assumes injectivity for contiguous \(3\times2\) rectangular blocks. -/
def IsThreeByTwoContiguousSquareLatticeRectangle {width height : ℕ}
    (R : Finset (SquareLatticeVertex width height)) : Prop :=
  ∃ xStart yStart : ℕ,
    xStart + 3 ≤ width ∧ yStart + 2 ≤ height ∧
      R = squareLatticeContiguousRectangle xStart yStart 3 2

/-- A bounded contiguous coordinate rectangle of width two and height three has
the \(2\times3\) source shape.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1452
of `Papers/1804.04964/paper_normal.tex`, where the proof assumes injectivity
for all \(2\times3\) rectangular blocks. -/
theorem isTwoByThreeContiguousSquareLatticeRectangle_of_bounds {width height : ℕ}
    {xStart yStart : ℕ} (hx : xStart + 2 ≤ width) (hy : yStart + 3 ≤ height) :
    IsTwoByThreeContiguousSquareLatticeRectangle
      (squareLatticeContiguousRectangle xStart yStart 2 3 :
        Finset (SquareLatticeVertex width height)) :=
  ⟨xStart, yStart, hx, hy, rfl⟩

/-- A bounded contiguous coordinate rectangle of width three and height two has
the \(3\times2\) source shape.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1452
of `Papers/1804.04964/paper_normal.tex`, where the proof assumes injectivity
for all \(3\times2\) rectangular blocks. -/
theorem isThreeByTwoContiguousSquareLatticeRectangle_of_bounds {width height : ℕ}
    {xStart yStart : ℕ} (hx : xStart + 3 ≤ width) (hy : yStart + 2 ≤ height) :
    IsThreeByTwoContiguousSquareLatticeRectangle
      (squareLatticeContiguousRectangle xStart yStart 3 2 :
        Finset (SquareLatticeVertex width height)) :=
  ⟨xStart, yStart, hx, hy, rfl⟩

/-- The displayed region \(R\) in the normal square-lattice proof.

It is the union of a contiguous \(2\times3\) rectangle and the overlapping
contiguous \(3\times2\) rectangle covering the upper two rows of the
\(2\times3\) block and extending one column to the right.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1430
of `Papers/1804.04964/paper_normal.tex`. -/
def normalSquareRegionR {width height : ℕ} (xStart yStart : ℕ) :
    Finset (SquareLatticeVertex width height) :=
  squareLatticeContiguousRectangle xStart yStart 2 3 ∪
    squareLatticeContiguousRectangle xStart (yStart + 1) 3 2

/-- The displayed region \(S\) in the normal square-lattice proof.

It is the union of two overlapping contiguous \(2\times3\) rectangles, shifted
by one horizontal coordinate.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1430
of `Papers/1804.04964/paper_normal.tex`. -/
def normalSquareRegionS {width height : ℕ} (xStart yStart : ℕ) :
    Finset (SquareLatticeVertex width height) :=
  squareLatticeContiguousRectangle xStart yStart 2 3 ∪
    squareLatticeContiguousRectangle (xStart + 1) yStart 2 3

/-- The displayed region \(R\) is the union of one contiguous \(2\times3\)
rectangle and one contiguous \(3\times2\) rectangle.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1430
of `Papers/1804.04964/paper_normal.tex`, where the source says that the
displayed region \(R\) is a union of smaller injective rectangles. -/
theorem normalSquareRegionR_rectangular_decomposition {width height : ℕ}
    {xStart yStart : ℕ} (hx : xStart + 3 ≤ width) (hy : yStart + 3 ≤ height) :
    ∃ R₂ R₃ : Finset (SquareLatticeVertex width height),
      IsTwoByThreeContiguousSquareLatticeRectangle R₂ ∧
        IsThreeByTwoContiguousSquareLatticeRectangle R₃ ∧
          normalSquareRegionR xStart yStart = R₂ ∪ R₃ := by
  refine ⟨squareLatticeContiguousRectangle xStart yStart 2 3,
    squareLatticeContiguousRectangle xStart (yStart + 1) 3 2, ?_, ?_, rfl⟩
  · exact isTwoByThreeContiguousSquareLatticeRectangle_of_bounds (by omega) hy
  · exact isThreeByTwoContiguousSquareLatticeRectangle_of_bounds hx (by omega)

/-- The displayed region \(S\) is the union of two contiguous \(2\times3\)
rectangles.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1430
of `Papers/1804.04964/paper_normal.tex`, where the source says that the
displayed region \(S\) is a union of smaller injective rectangles. -/
theorem normalSquareRegionS_rectangular_decomposition {width height : ℕ}
    {xStart yStart : ℕ} (hx : xStart + 3 ≤ width) (hy : yStart + 3 ≤ height) :
    ∃ S₁ S₂ : Finset (SquareLatticeVertex width height),
      IsTwoByThreeContiguousSquareLatticeRectangle S₁ ∧
        IsTwoByThreeContiguousSquareLatticeRectangle S₂ ∧
          normalSquareRegionS xStart yStart = S₁ ∪ S₂ := by
  refine ⟨squareLatticeContiguousRectangle xStart yStart 2 3,
    squareLatticeContiguousRectangle (xStart + 1) yStart 2 3, ?_, ?_, rfl⟩
  · exact isTwoByThreeContiguousSquareLatticeRectangle_of_bounds (by omega) hy
  · exact isTwoByThreeContiguousSquareLatticeRectangle_of_bounds (by omega) hy

/-- The vertical edge block removed from the local window in the displayed
region \(T\).

This is the \(2\times3\) block shown in the source picture.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1443
of `Papers/1804.04964/paper_normal.tex`. -/
def normalSquareRegionTVerticalBlock {width height : ℕ} (xStart yStart : ℕ) :
    Finset (SquareLatticeVertex width height) :=
  squareLatticeContiguousRectangle xStart (yStart + 2) 2 3

/-- The horizontal edge block removed from the local window in the displayed
region \(T\).

This is the shifted \(3\times2\) block shown in the source picture.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1443
of `Papers/1804.04964/paper_normal.tex`. -/
def normalSquareRegionTHorizontalBlock {width height : ℕ} (xStart yStart : ℕ) :
    Finset (SquareLatticeVertex width height) :=
  squareLatticeContiguousRectangle (xStart + 2) (yStart + 1) 3 2

/-- The two edge blocks removed from the local window in the displayed region
\(T\).

The first block is the \(2\times3\) vertical block and the second block is the
shifted \(3\times2\) horizontal block shown in the source picture.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1443
of `Papers/1804.04964/paper_normal.tex`. -/
def normalSquareRegionTHole {width height : ℕ} (xStart yStart : ℕ) :
    Finset (SquareLatticeVertex width height) :=
  normalSquareRegionTVerticalBlock xStart yStart ∪
    normalSquareRegionTHorizontalBlock xStart yStart

/-- The vertical edge block removed from the displayed \(T\)-region is a
contiguous \(2\times3\) rectangle.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1443
of `Papers/1804.04964/paper_normal.tex`. -/
theorem normalSquareRegionTVerticalBlock_rectangular {width height : ℕ}
    {xStart yStart : ℕ} (hx : xStart + 5 ≤ width) (hy : yStart + 5 ≤ height) :
    IsTwoByThreeContiguousSquareLatticeRectangle
      (normalSquareRegionTVerticalBlock xStart yStart :
        Finset (SquareLatticeVertex width height)) := by
  exact isTwoByThreeContiguousSquareLatticeRectangle_of_bounds (by omega) (by omega)

/-- The horizontal edge block removed from the displayed \(T\)-region is a
contiguous \(3\times2\) rectangle.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1443
of `Papers/1804.04964/paper_normal.tex`. -/
theorem normalSquareRegionTHorizontalBlock_rectangular {width height : ℕ}
    {xStart yStart : ℕ} (hx : xStart + 5 ≤ width) (hy : yStart + 5 ≤ height) :
    IsThreeByTwoContiguousSquareLatticeRectangle
      (normalSquareRegionTHorizontalBlock xStart yStart :
        Finset (SquareLatticeVertex width height)) := by
  exact isThreeByTwoContiguousSquareLatticeRectangle_of_bounds (by omega) (by omega)

/-- The two edge blocks removed in the displayed region \(T\) are one
contiguous \(2\times3\) rectangle and one contiguous \(3\times2\) rectangle.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1443
of `Papers/1804.04964/paper_normal.tex`, where the source depicts \(T\) as
the complement of the two shown edge blocks. -/
theorem normalSquareRegionTHole_rectangular_decomposition {width height : ℕ}
    {xStart yStart : ℕ} (hx : xStart + 5 ≤ width) (hy : yStart + 5 ≤ height) :
    ∃ T₂ T₃ : Finset (SquareLatticeVertex width height),
      IsTwoByThreeContiguousSquareLatticeRectangle T₂ ∧
        IsThreeByTwoContiguousSquareLatticeRectangle T₃ ∧
          normalSquareRegionTHole xStart yStart = T₂ ∪ T₃ := by
  refine ⟨normalSquareRegionTVerticalBlock xStart yStart,
    normalSquareRegionTHorizontalBlock xStart yStart, ?_, ?_, rfl⟩
  · exact normalSquareRegionTVerticalBlock_rectangular hx hy
  · exact normalSquareRegionTHorizontalBlock_rectangular hx hy

/-- The displayed region \(T\) in the normal square-lattice proof.

This local coordinate model records the part of the source picture lying inside
the displayed \(5\times6\) window: the window with the two edge blocks recorded
in `normalSquareRegionTHole` removed.  The injective complementary block used
later in the proof of Theorem 3 is a finite-lattice complement around an edge,
not yet this local-window region by itself.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1443
of `Papers/1804.04964/paper_normal.tex`, where the text states that \(T\) is
injective once the PEPS size is at least \(5\times6\). -/
def normalSquareRegionT {width height : ℕ} (xStart yStart : ℕ) :
    Finset (SquareLatticeVertex width height) :=
  squareLatticeContiguousRectangle xStart yStart 5 6 \
    normalSquareRegionTHole xStart yStart

/-- The finite-lattice complementary block around the edge in the normal
square-lattice proof.

This is the full finite square lattice with the two displayed edge blocks
removed.  In the proof of Theorem 3 it is the region denoted \(A_3\), the
third block after the red and blue edge blocks.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1499
of `Papers/1804.04964/paper_normal.tex`. -/
def normalSquareEdgeComplementRegion {width height : ℕ} (xStart yStart : ℕ) :
    Finset (SquareLatticeVertex width height) :=
  regionComplement (normalSquareRegionTHole xStart yStart)

@[simp] theorem mem_normalSquareRegionR {width height : ℕ}
    (xStart yStart : ℕ) (v : SquareLatticeVertex width height) :
    v ∈ normalSquareRegionR xStart yStart ↔
      (xStart ≤ v.1.1 ∧ v.1.1 < xStart + 2 ∧
        yStart ≤ v.2.1 ∧ v.2.1 < yStart + 3) ∨
      (xStart ≤ v.1.1 ∧ v.1.1 < xStart + 3 ∧
        yStart + 1 ≤ v.2.1 ∧ v.2.1 < yStart + 3) := by
  simp [normalSquareRegionR]

@[simp] theorem mem_normalSquareRegionS {width height : ℕ}
    (xStart yStart : ℕ) (v : SquareLatticeVertex width height) :
    v ∈ normalSquareRegionS xStart yStart ↔
      (xStart ≤ v.1.1 ∧ v.1.1 < xStart + 2 ∧
        yStart ≤ v.2.1 ∧ v.2.1 < yStart + 3) ∨
      (xStart + 1 ≤ v.1.1 ∧ v.1.1 < xStart + 3 ∧
        yStart ≤ v.2.1 ∧ v.2.1 < yStart + 3) := by
  simp [normalSquareRegionS]

@[simp] theorem mem_normalSquareRegionTVerticalBlock {width height : ℕ}
    (xStart yStart : ℕ) (v : SquareLatticeVertex width height) :
    v ∈ normalSquareRegionTVerticalBlock xStart yStart ↔
      xStart ≤ v.1.1 ∧ v.1.1 < xStart + 2 ∧
        yStart + 2 ≤ v.2.1 ∧ v.2.1 < yStart + 5 := by
  simp [normalSquareRegionTVerticalBlock]

@[simp] theorem mem_normalSquareRegionTHorizontalBlock {width height : ℕ}
    (xStart yStart : ℕ) (v : SquareLatticeVertex width height) :
    v ∈ normalSquareRegionTHorizontalBlock xStart yStart ↔
      xStart + 2 ≤ v.1.1 ∧ v.1.1 < xStart + 5 ∧
        yStart + 1 ≤ v.2.1 ∧ v.2.1 < yStart + 3 := by
  simp [normalSquareRegionTHorizontalBlock]

@[simp] theorem mem_normalSquareRegionTHole {width height : ℕ}
    (xStart yStart : ℕ) (v : SquareLatticeVertex width height) :
    v ∈ normalSquareRegionTHole xStart yStart ↔
      (xStart ≤ v.1.1 ∧ v.1.1 < xStart + 2 ∧
        yStart + 2 ≤ v.2.1 ∧ v.2.1 < yStart + 5) ∨
      (xStart + 2 ≤ v.1.1 ∧ v.1.1 < xStart + 5 ∧
        yStart + 1 ≤ v.2.1 ∧ v.2.1 < yStart + 3) := by
  simp [normalSquareRegionTHole]

@[simp] theorem mem_normalSquareRegionT {width height : ℕ}
    (xStart yStart : ℕ) (v : SquareLatticeVertex width height) :
    v ∈ normalSquareRegionT xStart yStart ↔
      xStart ≤ v.1.1 ∧ v.1.1 < xStart + 5 ∧
        yStart ≤ v.2.1 ∧ v.2.1 < yStart + 6 ∧
          v ∉ normalSquareRegionTHole xStart yStart := by
  simp [normalSquareRegionT, and_assoc]

@[simp] theorem mem_normalSquareEdgeComplementRegion {width height : ℕ}
    (xStart yStart : ℕ) (v : SquareLatticeVertex width height) :
    v ∈ normalSquareEdgeComplementRegion xStart yStart ↔
      v ∉ normalSquareRegionTHole xStart yStart := by
  simp [normalSquareEdgeComplementRegion]

/-- The two edge blocks removed from the displayed \(T\)-region lie inside the
local \(5\times6\) coordinate window.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1443
of `Papers/1804.04964/paper_normal.tex`, where \(T\) is drawn as the
complement of the two shown edge blocks inside the displayed window. -/
theorem normalSquareRegionTHole_subset_window {width height : ℕ}
    (xStart yStart : ℕ) :
    normalSquareRegionTHole xStart yStart ⊆
      (squareLatticeContiguousRectangle xStart yStart 5 6 :
        Finset (SquareLatticeVertex width height)) := by
  intro v hv
  rw [mem_normalSquareRegionTHole] at hv
  rw [mem_squareLatticeContiguousRectangle]
  rcases hv with hv | hv <;> omega

/-- The two edge blocks removed from the displayed \(T\)-region are disjoint.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1443
of `Papers/1804.04964/paper_normal.tex`. -/
theorem normalSquareRegionTVerticalBlock_disjoint_horizontalBlock {width height : ℕ}
    (xStart yStart : ℕ) :
    Disjoint
      (normalSquareRegionTVerticalBlock xStart yStart :
        Finset (SquareLatticeVertex width height))
      (normalSquareRegionTHorizontalBlock xStart yStart) := by
  rw [Finset.disjoint_left]
  intro v hvVertical hvHorizontal
  rw [mem_normalSquareRegionTVerticalBlock] at hvVertical
  rw [mem_normalSquareRegionTHorizontalBlock] at hvHorizontal
  omega

/-- The displayed \(T\)-region is disjoint from the two edge blocks removed
from the local \(5\times6\) window.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1443
of `Papers/1804.04964/paper_normal.tex`. -/
theorem normalSquareRegionT_disjoint_THole {width height : ℕ}
    (xStart yStart : ℕ) :
    Disjoint
      (normalSquareRegionT xStart yStart :
        Finset (SquareLatticeVertex width height))
      (normalSquareRegionTHole xStart yStart) := by
  unfold normalSquareRegionT
  exact disjoint_sdiff_self_left

/-- The displayed \(T\)-region is disjoint from the vertical edge block removed
from the local \(5\times6\) window.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1443
of `Papers/1804.04964/paper_normal.tex`. -/
theorem normalSquareRegionT_disjoint_verticalBlock {width height : ℕ}
    (xStart yStart : ℕ) :
    Disjoint
      (normalSquareRegionT xStart yStart :
        Finset (SquareLatticeVertex width height))
      (normalSquareRegionTVerticalBlock xStart yStart) := by
  rw [Finset.disjoint_left]
  intro v hvT hvVertical
  rw [mem_normalSquareRegionT] at hvT
  exact hvT.2.2.2.2 (by simp [normalSquareRegionTHole, hvVertical])

/-- The displayed \(T\)-region is disjoint from the horizontal edge block
removed from the local \(5\times6\) window.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1443
of `Papers/1804.04964/paper_normal.tex`. -/
theorem normalSquareRegionT_disjoint_horizontalBlock {width height : ℕ}
    (xStart yStart : ℕ) :
    Disjoint
      (normalSquareRegionT xStart yStart :
        Finset (SquareLatticeVertex width height))
      (normalSquareRegionTHorizontalBlock xStart yStart) := by
  rw [Finset.disjoint_left]
  intro v hvT hvHorizontal
  rw [mem_normalSquareRegionT] at hvT
  exact hvT.2.2.2.2 (by simp [normalSquareRegionTHole, hvHorizontal])

/-- The displayed \(T\)-region and the two removed edge blocks reconstruct the
local \(5\times6\) coordinate window.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1443
of `Papers/1804.04964/paper_normal.tex`. -/
theorem normalSquareRegionT_union_THole {width height : ℕ}
    (xStart yStart : ℕ) :
    normalSquareRegionT xStart yStart ∪ normalSquareRegionTHole xStart yStart =
      (squareLatticeContiguousRectangle xStart yStart 5 6 :
        Finset (SquareLatticeVertex width height)) := by
  unfold normalSquareRegionT
  exact Finset.sdiff_union_of_subset (normalSquareRegionTHole_subset_window xStart yStart)

/-- The displayed \(T\)-region, the vertical removed block, and the horizontal
removed block reconstruct the local \(5\times6\) coordinate window.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1443
of `Papers/1804.04964/paper_normal.tex`. -/
theorem normalSquareRegionT_union_verticalBlock_union_horizontalBlock {width height : ℕ}
    (xStart yStart : ℕ) :
    normalSquareRegionT xStart yStart ∪ normalSquareRegionTVerticalBlock xStart yStart ∪
        normalSquareRegionTHorizontalBlock xStart yStart =
      (squareLatticeContiguousRectangle xStart yStart 5 6 :
        Finset (SquareLatticeVertex width height)) := by
  rw [Finset.union_assoc]
  simpa [normalSquareRegionTHole] using normalSquareRegionT_union_THole xStart yStart

/-- The local-window \(T\)-region is contained in the finite-lattice
complementary block around the edge.

Source: arXiv:1804.04964, Section 3, lines 1430--1499 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem normalSquareRegionT_subset_edgeComplementRegion {width height : ℕ}
    (xStart yStart : ℕ) :
    normalSquareRegionT xStart yStart ⊆
      (normalSquareEdgeComplementRegion xStart yStart :
        Finset (SquareLatticeVertex width height)) := by
  intro v hv
  rw [mem_normalSquareRegionT] at hv
  rw [mem_normalSquareEdgeComplementRegion]
  exact hv.2.2.2.2

/-- The finite-lattice complementary block is disjoint from the two edge blocks
removed around the edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1499
of `Papers/1804.04964/paper_normal.tex`. -/
theorem normalSquareEdgeComplementRegion_disjoint_THole {width height : ℕ}
    (xStart yStart : ℕ) :
    Disjoint
      (normalSquareEdgeComplementRegion xStart yStart :
        Finset (SquareLatticeVertex width height))
      (normalSquareRegionTHole xStart yStart) := by
  unfold normalSquareEdgeComplementRegion regionComplement
  exact disjoint_sdiff_self_left

/-- The finite-lattice complementary block and the two edge blocks reconstruct
the full square lattice.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1499
of `Papers/1804.04964/paper_normal.tex`. -/
theorem normalSquareEdgeComplementRegion_union_THole {width height : ℕ}
    (xStart yStart : ℕ) :
    normalSquareEdgeComplementRegion xStart yStart ∪ normalSquareRegionTHole xStart yStart =
      (Finset.univ : Finset (SquareLatticeVertex width height)) := by
  unfold normalSquareEdgeComplementRegion regionComplement
  exact Finset.sdiff_union_of_subset (Finset.subset_univ _)

/-- The finite-lattice complementary block together with the vertical and
horizontal edge blocks reconstructs the full square lattice.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1499
of `Papers/1804.04964/paper_normal.tex`. -/
theorem normalSquareEdgeComplementRegion_union_verticalBlock_union_horizontalBlock
    {width height : ℕ} (xStart yStart : ℕ) :
    normalSquareEdgeComplementRegion xStart yStart ∪
        normalSquareRegionTVerticalBlock xStart yStart ∪
          normalSquareRegionTHorizontalBlock xStart yStart =
      (Finset.univ : Finset (SquareLatticeVertex width height)) := by
  rw [Finset.union_assoc]
  simpa [normalSquareRegionTHole] using
    normalSquareEdgeComplementRegion_union_THole xStart yStart

/-- The displayed region \(R\) is contained in the displayed region \(S\).

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1430
and 1544--1546 of `Papers/1804.04964/paper_normal.tex`. -/
theorem normalSquareRegionR_subset_regionS {width height : ℕ}
    (xStart yStart : ℕ) :
    normalSquareRegionR xStart yStart ⊆
      (normalSquareRegionS xStart yStart :
        Finset (SquareLatticeVertex width height)) := by
  intro v hv
  rw [mem_normalSquareRegionR] at hv
  rw [mem_normalSquareRegionS]
  rcases hv with hv | hv
  · exact Or.inl hv
  · rcases hv with ⟨hx0, hx3, hy1, hy3⟩
    by_cases hx2 : v.1.1 < xStart + 2
    · exact Or.inl ⟨hx0, hx2, by omega, hy3⟩
    · exact Or.inr ⟨by omega, hx3, by omega, hy3⟩

/-- The displayed regions \(R\) and \(S\) differ by the lower-right site of
the \(3\times3\) square.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1430
and 1544--1546 of `Papers/1804.04964/paper_normal.tex`. -/
@[simp] theorem mem_normalSquareRegionS_sdiff_regionR {width height : ℕ}
    (xStart yStart : ℕ) (v : SquareLatticeVertex width height) :
    v ∈ normalSquareRegionS xStart yStart \ normalSquareRegionR xStart yStart ↔
      v.1.1 = xStart + 2 ∧ v.2.1 = yStart := by
  rw [Finset.mem_sdiff, mem_normalSquareRegionS, mem_normalSquareRegionR]
  constructor
  · rintro ⟨hvS, hvR⟩
    rcases hvS with hvS | hvS
    · exfalso
      exact hvR (Or.inl hvS)
    · rcases hvS with ⟨hx1, hx3, hy0, hy3⟩
      by_contra h
      push Not at h
      apply hvR
      by_cases hy1 : yStart + 1 ≤ v.2.1
      · exact Or.inr ⟨by omega, hx3, hy1, hy3⟩
      · exact Or.inl ⟨by omega, by omega, hy0, by omega⟩
  · rintro ⟨hx, hy⟩
    constructor
    · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
    · rintro (hvR | hvR)
      · omega
      · omega

/-- One-site-different injective regions with injective complements.

The general normal PEPS theorem after Theorem 3 assumes that, for every site,
there are two injective regions with injective complements that differ exactly
at that site.  This structure records that hypothesis.

Source: arXiv:1804.04964, Section 3, theorem labelled `normal`, lines
1576--1583 of `Papers/1804.04964/paper_normal.tex`. -/
structure NormalOneSiteSeparationHypotheses where
  /-- The region containing the distinguished site. -/
  withSite : V → Finset V
  /-- The comparison region omitting the distinguished site. -/
  withoutSite : V → Finset V
  /-- The region containing the distinguished site is injective. -/
  withSite_injective : ∀ v : V, ι.IsInjective (withSite v)
  /-- The comparison region is injective. -/
  withoutSite_injective : ∀ v : V, ι.IsInjective (withoutSite v)
  /-- The complement of the first region is injective. -/
  withSite_complement_injective : ∀ v : V, ι.IsInjective (regionComplement (withSite v))
  /-- The complement of the comparison region is injective. -/
  withoutSite_complement_injective :
    ∀ v : V, ι.IsInjective (regionComplement (withoutSite v))
  /-- The distinguished site belongs to the first region. -/
  site_mem_withSite : ∀ v : V, v ∈ withSite v
  /-- The distinguished site does not belong to the comparison region. -/
  site_notMem_withoutSite : ∀ v : V, v ∉ withoutSite v
  /-- Away from the distinguished site, the two regions have the same vertices. -/
  agree_away :
    ∀ v w : V, w ≠ v → (w ∈ withSite v ↔ w ∈ withoutSite v)

namespace NormalOneSiteSeparationHypotheses

variable {ι}

/-- The two regions in the one-site comparison differ exactly at the
distinguished site. -/
theorem mem_withSite_iff (h : NormalOneSiteSeparationHypotheses ι) (v w : V) :
    w ∈ h.withSite v ↔ w = v ∨ w ∈ h.withoutSite v := by
  constructor
  · intro hw
    by_cases hvw : w = v
    · exact Or.inl hvw
    · exact Or.inr ((h.agree_away v w hvw).mp hw)
  · intro hw
    rcases hw with rfl | hw
    · exact h.site_mem_withSite w
    · by_cases hvw : w = v
      · subst w
        exact absurd hw (h.site_notMem_withoutSite v)
      · exact ((h.agree_away v w hvw).mpr hw)

end NormalOneSiteSeparationHypotheses

section GeneralBlocking

variable [LinearOrder V]

/-- General normal PEPS blocking hypotheses.

These are the two hypotheses stated in the general normal PEPS theorem after
Theorem 3 of arXiv:1804.04964: edge-centred blockings into three injective
regions, and one-site-different injective regions with injective complements.
Source: arXiv:1804.04964, Section 3, theorem labelled `normal`, lines
1576--1583 of `Papers/1804.04964/paper_normal.tex`. -/
structure NormalPEPSBlockingHypotheses (G : SimpleGraph V) where
  /-- Blocking around every edge gives a three-region injective chain. -/
  edgeBlocking : NormalEdgeBlockingHypotheses ι G
  /-- Every site admits one-site-different injective comparison regions. -/
  oneSiteSeparation : NormalOneSiteSeparationHypotheses ι

namespace NormalPEPSBlockingHypotheses

variable {ι} {G : SimpleGraph V}

/-- The normal PEPS blocking hypotheses supply the three injective regions
around every edge.

Source: arXiv:1804.04964, Section 3, theorem labelled `normal`, lines
1576--1583 of `Papers/1804.04964/paper_normal.tex`. -/
theorem injective_chain_at_edge (h : NormalPEPSBlockingHypotheses ι G) (e : Edge G) :
    ι.IsInjective (h.edgeBlocking.red e) ∧
      ι.IsInjective (h.edgeBlocking.blue e) ∧
      ι.IsInjective (h.edgeBlocking.complement e) :=
  h.edgeBlocking.injective_chain_at_edge e

/-- The normal PEPS blocking hypotheses supply endpoint membership,
pairwise disjointness, and coverage for the three regions around every edge.

Source: arXiv:1804.04964, Section 3, theorem labelled `normal`, lines
1576--1583 of `Papers/1804.04964/paper_normal.tex`. -/
theorem endpoint_disjoint_cover_at_edge
    (h : NormalPEPSBlockingHypotheses ι G) (e : Edge G) :
    e.1.1 ∈ h.edgeBlocking.red e ∧ e.1.2 ∈ h.edgeBlocking.blue e ∧
      Disjoint (h.edgeBlocking.red e) (h.edgeBlocking.blue e) ∧
      Disjoint (h.edgeBlocking.red e) (h.edgeBlocking.complement e) ∧
      Disjoint (h.edgeBlocking.blue e) (h.edgeBlocking.complement e) ∧
      h.edgeBlocking.red e ∪ h.edgeBlocking.blue e ∪
          h.edgeBlocking.complement e = Finset.univ :=
  h.edgeBlocking.endpoint_disjoint_cover_at_edge e

/-- The one-site part of the normal PEPS blocking hypotheses says that the
region containing a site is obtained from the comparison region by adding
that site.

Source: arXiv:1804.04964, Section 3, theorem labelled `normal`, lines
1576--1583 of `Papers/1804.04964/paper_normal.tex`. -/
theorem mem_withSite_iff (h : NormalPEPSBlockingHypotheses ι G) (v w : V) :
    w ∈ h.oneSiteSeparation.withSite v ↔
      w = v ∨ w ∈ h.oneSiteSeparation.withoutSite v :=
  h.oneSiteSeparation.mem_withSite_iff v w

end NormalPEPSBlockingHypotheses

end GeneralBlocking

/-- Rectangular injectivity hypotheses for the square-lattice normal PEPS
theorem.

Theorem 3 of arXiv:1804.04964 assumes injectivity for every \(2\times 3\) and
\(3\times 2\) rectangle.  The hypotheses specify the two families of
rectangular regions and their injectivity assertions, without choosing a
coordinate model for the square lattice.
Source: arXiv:1804.04964, Section 3, lines 1407--1452 of
`Papers/1804.04964/paper_normal.tex`. -/
structure NormalRectangleInjectivityHypotheses where
  /-- The finite regions regarded as \(2\times 3\) rectangles. -/
  IsTwoByThreeRegion : Finset V → Prop
  /-- The finite regions regarded as \(3\times 2\) rectangles. -/
  IsThreeByTwoRegion : Finset V → Prop
  /-- Every \(2\times 3\) rectangular region is injective. -/
  twoByThree_injective : ∀ R : Finset V, IsTwoByThreeRegion R → ι.IsInjective R
  /-- Every \(3\times 2\) rectangular region is injective. -/
  threeByTwo_injective : ∀ R : Finset V, IsThreeByTwoRegion R → ι.IsInjective R

/-- Coordinate square-lattice form of the rectangular injectivity hypotheses.

Theorem 3 of arXiv:1804.04964 assumes injectivity for every contiguous
\(2\times 3\) and \(3\times 2\) rectangular block in the finite square
lattice. This is the coordinate specialization of
`NormalRectangleInjectivityHypotheses` to the vertex set
`SquareLatticeVertex width height`.

Source: arXiv:1804.04964, Section 3, Theorem 3 and proof, lines 1407--1452
of `Papers/1804.04964/paper_normal.tex`. -/
structure NormalSquareLatticeRectangleInjectivityHypotheses {width height : ℕ}
    (κ : RegionInjectivityData (SquareLatticeVertex width height)) where
  /-- Every contiguous \(2\times 3\) coordinate rectangle is injective. -/
  twoByThree_injective :
    ∀ R : Finset (SquareLatticeVertex width height),
      IsTwoByThreeContiguousSquareLatticeRectangle R → κ.IsInjective R
  /-- Every contiguous \(3\times 2\) coordinate rectangle is injective. -/
  threeByTwo_injective :
    ∀ R : Finset (SquareLatticeVertex width height),
      IsThreeByTwoContiguousSquareLatticeRectangle R → κ.IsInjective R

namespace NormalSquareLatticeRectangleInjectivityHypotheses

variable {width height : ℕ}
variable {κ : RegionInjectivityData (SquareLatticeVertex width height)}

/-- The coordinate square-lattice rectangular hypotheses as abstract
rectangular injectivity hypotheses.

Source: arXiv:1804.04964, Section 3, Theorem 3 and proof, lines 1407--1452
of `Papers/1804.04964/paper_normal.tex`. -/
def toRectangular
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ) :
    NormalRectangleInjectivityHypotheses κ where
  IsTwoByThreeRegion := IsTwoByThreeContiguousSquareLatticeRectangle
  IsThreeByTwoRegion := IsThreeByTwoContiguousSquareLatticeRectangle
  twoByThree_injective := h.twoByThree_injective
  threeByTwo_injective := h.threeByTwo_injective

@[simp] theorem toRectangular_twoByThreeRegion
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (R : Finset (SquareLatticeVertex width height)) :
    h.toRectangular.IsTwoByThreeRegion R ↔
      IsTwoByThreeContiguousSquareLatticeRectangle R :=
  Iff.rfl

@[simp] theorem toRectangular_threeByTwoRegion
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (R : Finset (SquareLatticeVertex width height)) :
    h.toRectangular.IsThreeByTwoRegion R ↔
      IsThreeByTwoContiguousSquareLatticeRectangle R :=
  Iff.rfl

/-- A bounded contiguous \(2\times3\) coordinate rectangle is injective under
the square-lattice rectangular injectivity hypotheses.

Source: arXiv:1804.04964, Section 3, Theorem 3 and proof, lines 1407--1452
of `Papers/1804.04964/paper_normal.tex`. -/
theorem rect23_injective
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    {xStart yStart : ℕ} (hx : xStart + 2 ≤ width) (hy : yStart + 3 ≤ height) :
    κ.IsInjective
      (squareLatticeContiguousRectangle xStart yStart 2 3 :
        Finset (SquareLatticeVertex width height)) :=
  h.twoByThree_injective _
    (isTwoByThreeContiguousSquareLatticeRectangle_of_bounds hx hy)

/-- A bounded contiguous \(3\times2\) coordinate rectangle is injective under
the square-lattice rectangular injectivity hypotheses.

Source: arXiv:1804.04964, Section 3, Theorem 3 and proof, lines 1407--1452
of `Papers/1804.04964/paper_normal.tex`. -/
theorem rect32_injective
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    {xStart yStart : ℕ} (hx : xStart + 3 ≤ width) (hy : yStart + 2 ≤ height) :
    κ.IsInjective
      (squareLatticeContiguousRectangle xStart yStart 3 2 :
        Finset (SquareLatticeVertex width height)) :=
  h.threeByTwo_injective _
    (isThreeByTwoContiguousSquareLatticeRectangle_of_bounds hx hy)

/-- The vertical edge block removed from the displayed \(T\)-region is injective
under the square-lattice rectangular injectivity hypotheses.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1405--1444
of `Papers/1804.04964/paper_normal.tex`. -/
theorem tVerticalBlock_injective
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    {xStart yStart : ℕ} (hx : xStart + 5 ≤ width) (hy : yStart + 5 ≤ height) :
    κ.IsInjective (normalSquareRegionTVerticalBlock xStart yStart) :=
  h.twoByThree_injective _
    (normalSquareRegionTVerticalBlock_rectangular hx hy)

/-- The horizontal edge block removed from the displayed \(T\)-region is
injective under the square-lattice rectangular injectivity hypotheses.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1405--1444
of `Papers/1804.04964/paper_normal.tex`. -/
theorem tHorizontalBlock_injective
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    {xStart yStart : ℕ} (hx : xStart + 5 ≤ width) (hy : yStart + 5 ≤ height) :
    κ.IsInjective (normalSquareRegionTHorizontalBlock xStart yStart) :=
  h.threeByTwo_injective _
    (normalSquareRegionTHorizontalBlock_rectangular hx hy)

/-- The union of the two edge blocks removed from the displayed \(T\)-region is
injective once rectangular injectivity is combined with the union-closure
assertion from the source injective-union lemma.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union and proof of
Theorem 3, lines 1322--1444 of `Papers/1804.04964/paper_normal.tex`. -/
theorem tHole_injective_of_union
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    {xStart yStart : ℕ} (hx : xStart + 5 ≤ width) (hy : yStart + 5 ≤ height) :
    κ.IsInjective (normalSquareRegionTHole xStart yStart) := by
  unfold normalSquareRegionTHole
  exact hUnion.union_injective
    (h.tVerticalBlock_injective hx hy)
    (h.tHorizontalBlock_injective hx hy)

/-- Region \(R\) is injective once rectangular injectivity is combined with
the union-closure assertion from the source injective-union lemma.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union and proof of
Theorem 3, lines 1322--1430 of `Papers/1804.04964/paper_normal.tex`. -/
theorem regionR_injective_of_union
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    {xStart yStart : ℕ} (hx : xStart + 3 ≤ width) (hy : yStart + 3 ≤ height) :
    κ.IsInjective (normalSquareRegionR xStart yStart) := by
  rcases normalSquareRegionR_rectangular_decomposition hx hy with
    ⟨R₂, R₃, hR₂, hR₃, hR⟩
  rw [hR]
  exact hUnion.union_injective
    (h.twoByThree_injective R₂ hR₂)
    (h.threeByTwo_injective R₃ hR₃)

/-- Region \(S\) is injective once rectangular injectivity is combined with
the union-closure assertion from the source injective-union lemma.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union and proof of
Theorem 3, lines 1322--1430 of `Papers/1804.04964/paper_normal.tex`. -/
theorem regionS_injective_of_union
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    {xStart yStart : ℕ} (hx : xStart + 3 ≤ width) (hy : yStart + 3 ≤ height) :
    κ.IsInjective (normalSquareRegionS xStart yStart) := by
  rcases normalSquareRegionS_rectangular_decomposition hx hy with
    ⟨S₁, S₂, hS₁, hS₂, hS⟩
  rw [hS]
  exact hUnion.union_injective
    (h.twoByThree_injective S₁ hS₁)
    (h.twoByThree_injective S₂ hS₂)

end NormalSquareLatticeRectangleInjectivityHypotheses

/-- Square-lattice normal PEPS blocking hypotheses for Theorem 3.

This records the hypotheses used in the translationally invariant square-lattice
case: all \(2\times 3\) and \(3\times 2\) regions are injective, the lattice is
large enough for the edge-blocking proof, and the specific \(R\), \(S\), and
\(T\) regions used in the source proof are injective.  The geometric statement
that the displayed regions are unions of smaller injective rectangles is left
to the tensor-level region-injectivity theorem.

**Scope restriction (R/S/T injectivity):** This structure assumes injectivity
of \(R\), \(S\), and \(T\) directly, whereas arXiv:1804.04964, Section 3
derives those assertions from rectangular injectivity and the
union-of-injective-regions argument. The authoritative source comparison and
elimination plan are
`docs/paper-gaps/peps_normal_ft_section3_route.tex`, Section
"Remaining mathematical obligations".

Source: arXiv:1804.04964, Section 3, Theorem 3 and its proof, lines
1407--1504 of `Papers/1804.04964/paper_normal.tex`. -/
structure NormalSquareBlockingRegions where
  /-- Horizontal size parameter in Theorem 3. -/
  width : ℕ
  /-- Vertical size parameter in Theorem 3. -/
  height : ℕ
  /-- The square-lattice proof assumes width at least seven. -/
  seven_le_width : 7 ≤ width
  /-- The square-lattice proof assumes height at least seven. -/
  seven_le_height : 7 ≤ height
  /-- The finite vertex set has the cardinality of the \(width\times height\)
  rectangular square-lattice region under consideration. -/
  card_eq_width_mul_height : Fintype.card V = width * height
  /-- The rectangular injectivity assumptions of Theorem 3. -/
  rectangles : NormalRectangleInjectivityHypotheses ι
  /-- The region \(R\) used in the one-site comparison. -/
  regionR : Finset V
  /-- The region \(S\) used in the one-site comparison. -/
  regionS : Finset V
  /-- The region \(T\) used as the complementary injective block. -/
  regionT : Finset V
  /-- Region \(R\) is injective. -/
  regionR_injective : ι.IsInjective regionR
  /-- Region \(S\) is injective. -/
  regionS_injective : ι.IsInjective regionS
  /-- Region \(T\) is injective. -/
  regionT_injective : ι.IsInjective regionT

end PEPS
end TNLean

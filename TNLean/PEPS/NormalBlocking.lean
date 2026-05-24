import Mathlib.Data.Finset.Prod

import TNLean.PEPS.Defs
import TNLean.PEPS.InjectiveRegion

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

section EdgeBlocking

variable [LinearOrder V]

/-- Edge-centred blocking into three injective regions.

For every edge, the normal PEPS proof blocks the network into a red region, a
blue region, and the complementary region.  The edge endpoints lie in the red
and blue regions respectively, the three regions are pairwise disjoint, their
union is the whole vertex set, and each region is injective.  This records the
hypotheses needed before applying the three-site injective-chain step.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500
of `Papers/1804.04964/paper_normal.tex`. -/
structure NormalEdgeBlockingHypotheses (G : SimpleGraph V) where
  /-- The first injective block around each edge. -/
  red : Edge G → Finset V
  /-- The second injective block around each edge. -/
  blue : Edge G → Finset V
  /-- The complementary injective block around each edge. -/
  complement : Edge G → Finset V
  /-- The left endpoint of the edge lies in the red block. -/
  left_mem_red : ∀ e : Edge G, e.1.1 ∈ red e
  /-- The right endpoint of the edge lies in the blue block. -/
  right_mem_blue : ∀ e : Edge G, e.1.2 ∈ blue e
  /-- The red block is injective. -/
  red_injective : ∀ e : Edge G, ι.IsInjective (red e)
  /-- The blue block is injective. -/
  blue_injective : ∀ e : Edge G, ι.IsInjective (blue e)
  /-- The complementary block is injective. -/
  complement_injective : ∀ e : Edge G, ι.IsInjective (complement e)
  /-- The red and blue blocks are disjoint. -/
  red_disjoint_blue : ∀ e : Edge G, Disjoint (red e) (blue e)
  /-- The red and complementary blocks are disjoint. -/
  red_disjoint_complement : ∀ e : Edge G, Disjoint (red e) (complement e)
  /-- The blue and complementary blocks are disjoint. -/
  blue_disjoint_complement : ∀ e : Edge G, Disjoint (blue e) (complement e)
  /-- The three edge-centred blocks cover the vertex set. -/
  cover_univ : ∀ e : Edge G, red e ∪ blue e ∪ complement e = Finset.univ

namespace NormalEdgeBlockingHypotheses

variable {ι}

/-- The edge-centred blocking supplies a three-region injective chain at every
edge. -/
theorem injective_chain_at_edge (h : NormalEdgeBlockingHypotheses ι G) (e : Edge G) :
    ι.IsInjective (h.red e) ∧ ι.IsInjective (h.blue e) ∧
      ι.IsInjective (h.complement e) :=
  ⟨h.red_injective e, h.blue_injective e, h.complement_injective e⟩

end NormalEdgeBlockingHypotheses

end EdgeBlocking

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

end NormalSquareLatticeRectangleInjectivityHypotheses

/-- Square-lattice normal PEPS blocking hypotheses for Theorem 3.

This records the hypotheses used in the translationally invariant square-lattice
case: all \(2\times 3\) and \(3\times 2\) regions are injective, the lattice is
large enough for the edge-blocking proof, and the specific \(R\), \(S\), and
\(T\) regions used in the source proof are injective.  The geometric statement
that the displayed regions are unions of smaller injective rectangles is left
to the tensor-level region-injectivity theorem.

**Scope restriction (R/S/T injectivity):** The injectivity assertions for
\(R\), \(S\), and \(T\) are assumed directly, whereas arXiv:1804.04964,
Section 3, derives them from the \(2\times 3\) and \(3\times 2\) rectangular
injectivity assumptions using the union-of-injective-regions lemma. The regions
\(R\), \(S\), and \(T\) are also not yet tied to the displayed square-lattice
geometry, to the two rectangular-region predicates, or to a square-lattice
coordinate and adjacency model; the size fields only record \(|V|=width\cdot
height\). This structure therefore does not yet supply the translated per-edge
red, blue, and complementary regions used in the proof of Theorem 3. Documented
in `docs/paper-gaps/peps_normal_ft_section3_route.tex`, Remaining mathematical
obligations 1--5. Elimination: introduce the coordinate-aware square-lattice
regions and derive these three assertions from rectangular injectivity after the
tensor-level union theorem is formalized.

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

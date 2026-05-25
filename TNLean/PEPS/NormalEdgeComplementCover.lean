import TNLean.PEPS.NormalBlocking

/-!
# Rectangular covers of the normal PEPS edge complement

This file records the conditional cover step for the finite-lattice
edge-complementary block \(A_3\) in the square-lattice normal PEPS proof.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, Lemma `lem:injective_union` and Theorem 3]
-/

namespace TNLean
namespace PEPS

/-- A finite rectangular cover of the edge-complementary block \(A_3\).

Each member of the cover is required to be one of the source-paper contiguous
\(2\times3\) or \(3\times2\) rectangles. Such a cover is a sufficient
coordinate condition for the union-of-injective-regions lemma to prove
injectivity of the finite-lattice complementary block.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1499
of `Papers/1804.04964/paper_normal.tex`. -/
structure NormalSquareEdgeComplementRectangleCover {width height : ℕ}
    (xStart yStart : ℕ) where
  /-- The finite index set labelling the rectangular pieces. -/
  Index : Type*
  /-- The finite family of pieces used in the cover. -/
  regions : Finset Index
  /-- The cover is nonempty, so finite union closure applies. -/
  nonempty : regions.Nonempty
  /-- The rectangular piece indexed by `i`. -/
  region : Index → Finset (SquareLatticeVertex width height)
  /-- Every piece is one of the two rectangular shapes assumed injective. -/
  rectangular :
    ∀ i ∈ regions,
      IsTwoByThreeContiguousSquareLatticeRectangle (region i) ∨
        IsThreeByTwoContiguousSquareLatticeRectangle (region i)
  /-- The rectangular pieces cover exactly the edge-complementary block. -/
  cover : regions.biUnion region = normalSquareEdgeComplementRegion xStart yStart

/-- In the normalized horizontal-edge \(5\times7\) frame, the finite-lattice
edge-complementary block is the local \(T\)-region together with two top-collar
contiguous \(3\times2\) rectangles.

This is the concrete set identity behind the passage from the local \(T\)
picture to the \(A_3\) block in the proof of Theorem 3.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1499
of `Papers/1804.04964/paper_normal.tex`. -/
theorem normalSquareEdgeComplementRegion_eq_T_union_topCollar :
    (normalSquareEdgeComplementRegion (width := 5) (height := 7) 0 0) =
      (normalSquareRegionT (width := 5) (height := 7) 0 0) ∪
        squareLatticeContiguousRectangle 0 5 3 2 ∪
          (squareLatticeContiguousRectangle 2 5 3 2 :
            Finset (SquareLatticeVertex 5 7)) := by
  ext v
  simp only [Finset.mem_union, mem_normalSquareEdgeComplementRegion, mem_normalSquareRegionT,
    mem_normalSquareRegionTHole, mem_squareLatticeContiguousRectangle]
  omega

namespace NormalSquareLatticeRectangleInjectivityHypotheses

variable {width height : ℕ}
variable {κ : RegionInjectivityData (SquareLatticeVertex width height)}

/-- The finite-lattice edge-complementary block is injective once it is covered
by source-paper \(2\times3\) and \(3\times2\) rectangles.

This is the formal conditional step for the block denoted \(A_3\) in the proof
of Theorem 3. It does not construct the cover; it states that rectangular
injectivity plus the union-of-injective-regions lemma proves injectivity after
the coordinate cover is supplied.

Source: arXiv:1804.04964, Section 3, Lemma `lem:injective_union` and proof of
Theorem 3, lines 1322--1499 of `Papers/1804.04964/paper_normal.tex`. -/
theorem edgeComplement_injective
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    {xStart yStart : ℕ}
    (cover : NormalSquareEdgeComplementRectangleCover (width := width) (height := height)
      xStart yStart) :
    κ.IsInjective (normalSquareEdgeComplementRegion xStart yStart) := by
  rw [← cover.cover]
  exact hUnion.biUnion_injective cover.nonempty cover.region fun i hi ↦ by
    rcases cover.rectangular i hi with hRect | hRect
    · exact h.twoByThree_injective _ hRect
    · exact h.threeByTwo_injective _ hRect

/-- In the normalized horizontal-edge \(5\times7\) frame, the edge-complementary
block is injective if the local \(T\)-region is injective.

The two additional top-collar regions are contiguous \(3\times2\) rectangles,
so rectangular injectivity and the union-of-injective-regions lemma add them to
the local \(T\)-region.

Source: arXiv:1804.04964, Section 3, Lemma `lem:injective_union` and proof of
Theorem 3, lines 1322--1499 of `Papers/1804.04964/paper_normal.tex`. -/
theorem topCollar_injective
    {κ : RegionInjectivityData (SquareLatticeVertex 5 7)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hT : κ.IsInjective (normalSquareRegionT (width := 5) (height := 7) 0 0)) :
    κ.IsInjective (normalSquareEdgeComplementRegion (width := 5) (height := 7) 0 0) := by
  rw [normalSquareEdgeComplementRegion_eq_T_union_topCollar]
  exact hUnion.union_injective
    (hUnion.union_injective hT (h.rect32_injective (by omega) (by omega)))
    (h.rect32_injective (by omega) (by omega))

end NormalSquareLatticeRectangleInjectivityHypotheses

end PEPS
end TNLean

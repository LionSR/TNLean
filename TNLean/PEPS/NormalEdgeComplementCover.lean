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
\(2\times3\) or \(3\times2\) rectangles. The existence of such a cover is the
remaining coordinate assertion needed before the union-of-injective-regions
lemma can prove injectivity of the finite-lattice complementary block.

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

end NormalSquareLatticeRectangleInjectivityHypotheses

end PEPS
end TNLean

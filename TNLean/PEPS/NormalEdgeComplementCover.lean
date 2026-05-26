import TNLean.PEPS.NormalBlocking

/-!
# Rectangular covers in the normal PEPS proof

This file records the parametric rectangular-cover structure and the
conditional injectivity criteria for the local displayed \(T\)-region and the
finite-lattice edge-complementary block \(A_3\) in the square-lattice normal
PEPS proof.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, Lemma `lem:injective_union` and Theorem 3]
-/

namespace TNLean
namespace PEPS

/-- A finite rectangular cover of a square-lattice region.

Each member of the cover is required to be one of the source-paper contiguous
\(2\times3\) or \(3\times2\) rectangles. Such a cover is a sufficient coordinate
condition for the union-of-injective-regions lemma to prove injectivity of the
target region.

Source: arXiv:1804.04964, Section 3, Lemma `lem:injective_union` and proof of
Theorem 3, lines 1322--1499 of `Papers/1804.04964/paper_normal.tex`. -/
structure SquareLatticeRectangleCover {width height : ℕ}
    (target : Finset (SquareLatticeVertex width height)) where
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
  /-- The rectangular pieces cover exactly the target region. -/
  cover : regions.biUnion region = target

/-- A finite rectangular cover of the displayed local \(T\)-region.

Each member of the cover is required to be one of the source-paper contiguous
\(2\times3\) or \(3\times2\) rectangles. Such a cover is a sufficient
coordinate condition for the union-of-injective-regions lemma to prove
injectivity of \(T\).

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1444
of `Papers/1804.04964/paper_normal.tex`. -/
abbrev NormalSquareRegionTRectangleCover {width height : ℕ} (xStart yStart : ℕ) :=
  SquareLatticeRectangleCover
    (normalSquareRegionT (width := width) (height := height) xStart yStart)

/-- A finite rectangular cover of the edge-complementary block \(A_3\).

Each member of the cover is required to be one of the source-paper contiguous
\(2\times3\) or \(3\times2\) rectangles. Such a cover is a sufficient
coordinate condition for the union-of-injective-regions lemma to prove
injectivity of the finite-lattice complementary block.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1499
of `Papers/1804.04964/paper_normal.tex`. -/
abbrev NormalSquareEdgeComplementRectangleCover {width height : ℕ} (xStart yStart : ℕ) :=
  SquareLatticeRectangleCover
    (normalSquareEdgeComplementRegion (width := width) (height := height) xStart yStart)

/-- The current normalized \(5\times6\) local-window model for \(T\) has no
rectangular cover by contained source-paper \(2\times3\) and \(3\times2\)
rectangles.

This is a diagnostic statement about the present coordinate model
`normalSquareRegionT`, not a claim about the source theorem.  The source says
that \(T\) is injective for sufficiently large PEPS; this lemma records that
the present local-window complement is not yet the source rectangular cover
needed to prove that sentence.

Source context: arXiv:1804.04964, Section 3, proof of Theorem 3,
lines 1430--1444 of `Papers/1804.04964/paper_normal.tex`. -/
theorem not_normalSquareRegionT_rectangleCover_five_by_six :
    ¬ Nonempty (NormalSquareRegionTRectangleCover (width := 5) (height := 6) 0 0) := by
  rintro ⟨cover⟩
  let p : SquareLatticeVertex 5 6 := (⟨0, by omega⟩, ⟨0, by omega⟩)
  have hpT : p ∈ normalSquareRegionT (width := 5) (height := 6) 0 0 := by
    simp [p]
  have hpUnion : p ∈ cover.regions.biUnion cover.region := by
    rw [cover.cover]
    exact hpT
  rcases Finset.mem_biUnion.mp hpUnion with ⟨i, hi, hpi⟩
  rcases cover.rectangular i hi with hRect | hRect
  · rcases hRect with ⟨xStart, yStart, _hx, _hy, hRegion⟩
    let q : SquareLatticeVertex 5 6 := (⟨0, by omega⟩, ⟨2, by omega⟩)
    have hpRect :
        p ∈ (squareLatticeContiguousRectangle xStart yStart 2 3 :
          Finset (SquareLatticeVertex 5 6)) := by
      simpa [hRegion] using hpi
    have hqRect :
        q ∈ (squareLatticeContiguousRectangle xStart yStart 2 3 :
          Finset (SquareLatticeVertex 5 6)) := by
      rw [mem_squareLatticeContiguousRectangle] at hpRect ⊢
      simp [p, q] at hpRect ⊢
      omega
    have hqRegion : q ∈ cover.region i := by
      simpa [hRegion] using hqRect
    have hqUnion : q ∈ cover.regions.biUnion cover.region :=
      Finset.mem_biUnion.mpr ⟨i, hi, hqRegion⟩
    have hqT : q ∈ normalSquareRegionT (width := 5) (height := 6) 0 0 := by
      rwa [cover.cover] at hqUnion
    have hqNotT : q ∉ normalSquareRegionT (width := 5) (height := 6) 0 0 := by
      simp [q]
    exact hqNotT hqT
  · rcases hRect with ⟨xStart, yStart, _hx, _hy, hRegion⟩
    let q : SquareLatticeVertex 5 6 := (⟨2, by omega⟩, ⟨1, by omega⟩)
    have hpRect :
        p ∈ (squareLatticeContiguousRectangle xStart yStart 3 2 :
          Finset (SquareLatticeVertex 5 6)) := by
      simpa [hRegion] using hpi
    have hqRect :
        q ∈ (squareLatticeContiguousRectangle xStart yStart 3 2 :
          Finset (SquareLatticeVertex 5 6)) := by
      rw [mem_squareLatticeContiguousRectangle] at hpRect ⊢
      simp [p, q] at hpRect ⊢
      omega
    have hqRegion : q ∈ cover.region i := by
      simpa [hRegion] using hqRect
    have hqUnion : q ∈ cover.regions.biUnion cover.region :=
      Finset.mem_biUnion.mpr ⟨i, hi, hqRegion⟩
    have hqT : q ∈ normalSquareRegionT (width := 5) (height := 6) 0 0 := by
      rwa [cover.cover] at hqUnion
    have hqNotT : q ∉ normalSquareRegionT (width := 5) (height := 6) 0 0 := by
      simp [q]
    exact hqNotT hqT

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

/-- In the normalized vertical-edge \(7\times5\) frame, the finite-lattice
edge-complementary block is the local \(T\)-region together with two right-collar
contiguous \(2\times3\) rectangles.

This is the vertical-edge counterpart of
`normalSquareEdgeComplementRegion_eq_T_union_topCollar`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1499
of `Papers/1804.04964/paper_normal.tex`. -/
theorem normalSquareEdgeComplementRegion_eq_T_union_rightCollar :
    (normalSquareEdgeComplementRegion (width := 7) (height := 5) 0 0) =
      (normalSquareRegionT (width := 7) (height := 5) 0 0) ∪
        squareLatticeContiguousRectangle 5 0 2 3 ∪
          (squareLatticeContiguousRectangle 5 2 2 3 :
            Finset (SquareLatticeVertex 7 5)) := by
  ext v
  simp only [Finset.mem_union, mem_normalSquareEdgeComplementRegion, mem_normalSquareRegionT,
    mem_normalSquareRegionTHole, mem_squareLatticeContiguousRectangle]
  omega

/-- The removed blocks in the rotated local \(T\)-region for a vertical edge.

This is the \(7\times5\) counterpart of the red and blue blocks in the source
edge-blocking picture.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def normalSquareVerticalRegionTHole {width height : ℕ} (xStart yStart : ℕ) :
    Finset (SquareLatticeVertex width height) :=
  squareLatticeContiguousRectangle (xStart + 2) yStart 3 2 ∪
    squareLatticeContiguousRectangle (xStart + 1) (yStart + 2) 2 3

/-- The rotated local \(T\)-region used for the normalized vertical edge.

It is the complement, inside a \(6\times5\) local window, of the two blocks
adjacent to the vertical edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def normalSquareVerticalRegionT {width height : ℕ} (xStart yStart : ℕ) :
    Finset (SquareLatticeVertex width height) :=
  squareLatticeContiguousRectangle xStart yStart 6 5 \
    normalSquareVerticalRegionTHole xStart yStart

@[simp] theorem mem_normalSquareVerticalRegionTHole {width height : ℕ}
    (xStart yStart : ℕ) (v : SquareLatticeVertex width height) :
    v ∈ normalSquareVerticalRegionTHole xStart yStart ↔
      v ∈ squareLatticeContiguousRectangle (xStart + 2) yStart 3 2 ∨
        v ∈ squareLatticeContiguousRectangle (xStart + 1) (yStart + 2) 2 3 := by
  simp [normalSquareVerticalRegionTHole]

@[simp] theorem mem_normalSquareVerticalRegionT {width height : ℕ}
    (xStart yStart : ℕ) (v : SquareLatticeVertex width height) :
    v ∈ normalSquareVerticalRegionT xStart yStart ↔
      v ∈ squareLatticeContiguousRectangle xStart yStart 6 5 ∧
        v ∉ normalSquareVerticalRegionTHole xStart yStart := by
  simp [normalSquareVerticalRegionT]

/-- A finite rectangular cover of the rotated vertical local \(T\)-region.

This is the \(7\times5\) counterpart of `NormalSquareRegionTRectangleCover`
used for the normalized vertical-edge construction.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1500
of `Papers/1804.04964/paper_normal.tex`. -/
abbrev NormalSquareVerticalRegionTRectangleCover {width height : ℕ}
    (xStart yStart : ℕ) :=
  SquareLatticeRectangleCover
    (normalSquareVerticalRegionT (width := width) (height := height) xStart yStart)

/-- In the normalized vertical-edge \(7\times5\) frame, the complement of the
rotated red and blue edge blocks is the rotated local \(T\)-region together
with two right-collar contiguous \(2\times3\) rectangles.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem normalSquareVerticalEdgeComplement_eq_verticalT_union_rightCollar :
    (regionComplement
        (squareLatticeContiguousRectangle 2 0 3 2 ∪
          (squareLatticeContiguousRectangle 1 2 2 3 :
            Finset (SquareLatticeVertex 7 5)))) =
      (normalSquareVerticalRegionT (width := 7) (height := 5) 0 0) ∪
        squareLatticeContiguousRectangle 5 0 2 3 ∪
          (squareLatticeContiguousRectangle 5 2 2 3 :
            Finset (SquareLatticeVertex 7 5)) := by
  ext v
  simp only [Finset.mem_union, mem_regionComplement, mem_normalSquareVerticalRegionT,
    mem_normalSquareVerticalRegionTHole, mem_squareLatticeContiguousRectangle]
  omega

namespace NormalSquareLatticeRectangleInjectivityHypotheses

variable {width height : ℕ}
variable {κ : RegionInjectivityData (SquareLatticeVertex width height)}

/-- A square-lattice region is injective once it is covered by source-paper
\(2\times3\) and \(3\times2\) rectangles.

This is the common conditional step for the local \(T\)-region and for the
edge-complementary block \(A_3\). It states that rectangular injectivity plus
the union-of-injective-regions lemma proves injectivity once the coordinate
cover is supplied.

Source: arXiv:1804.04964, Section 3, Lemma `lem:injective_union` and proof of
Theorem 3, lines 1322--1499 of `Papers/1804.04964/paper_normal.tex`. -/
theorem injective_of_rectangleCover
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    {target : Finset (SquareLatticeVertex width height)}
    (cover : SquareLatticeRectangleCover target) :
    κ.IsInjective target := by
  rw [← cover.cover]
  exact hUnion.biUnion_injective cover.nonempty cover.region fun i hi ↦ by
    rcases cover.rectangular i hi with hRect | hRect
    · exact h.twoByThree_injective _ hRect
    · exact h.threeByTwo_injective _ hRect

/-- The displayed local \(T\)-region is injective once it is covered by
source-paper \(2\times3\) and \(3\times2\) rectangles.

This is the formal conditional step for the source sentence that \(T\) is
injective when the PEPS is large enough. It does not construct the cover; it
states that rectangular injectivity plus the union-of-injective-regions lemma
proves injectivity once the coordinate cover is supplied.

Source: arXiv:1804.04964, Section 3, Lemma `lem:injective_union` and proof of
Theorem 3, lines 1322--1444 of `Papers/1804.04964/paper_normal.tex`. -/
theorem regionT_injective_of_cover
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    {xStart yStart : ℕ}
    (cover : NormalSquareRegionTRectangleCover (width := width) (height := height)
      xStart yStart) :
    κ.IsInjective (normalSquareRegionT xStart yStart) :=
  h.injective_of_rectangleCover hUnion cover

/-- The rotated vertical local \(T\)-region is injective once it is covered by
source-paper \(2\times3\) and \(3\times2\) rectangles.

This is the vertical counterpart of `regionT_injective_of_cover`. It does not
construct the cover; it records the conditional passage from a source-sized
rectangular cover to injectivity.

Source: arXiv:1804.04964, Section 3, Lemma `lem:injective_union` and proof of
Theorem 3, lines 1322--1500 of `Papers/1804.04964/paper_normal.tex`. -/
theorem verticalT_inj_of_cover
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    {xStart yStart : ℕ}
    (cover : NormalSquareVerticalRegionTRectangleCover
      (width := width) (height := height) xStart yStart) :
    κ.IsInjective (normalSquareVerticalRegionT xStart yStart) :=
  h.injective_of_rectangleCover hUnion cover

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
    κ.IsInjective (normalSquareEdgeComplementRegion xStart yStart) :=
  h.injective_of_rectangleCover hUnion cover

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

/-- In the normalized vertical-edge \(7\times5\) frame, the edge-complementary
block is injective if the local \(T\)-region is injective.

The two additional right-collar regions are contiguous \(2\times3\) rectangles,
so rectangular injectivity and the union-of-injective-regions lemma add them to
the local \(T\)-region.

Source: arXiv:1804.04964, Section 3, Lemma `lem:injective_union` and proof of
Theorem 3, lines 1322--1499 of `Papers/1804.04964/paper_normal.tex`. -/
theorem rightCollar_injective
    {κ : RegionInjectivityData (SquareLatticeVertex 7 5)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hT : κ.IsInjective (normalSquareRegionT (width := 7) (height := 5) 0 0)) :
    κ.IsInjective (normalSquareEdgeComplementRegion (width := 7) (height := 5) 0 0) := by
  rw [normalSquareEdgeComplementRegion_eq_T_union_rightCollar]
  exact hUnion.union_injective
    (hUnion.union_injective hT (h.rect23_injective (by omega) (by omega)))
    (h.rect23_injective (by omega) (by omega))

/-- In the normalized vertical-edge \(7\times5\) frame, the actual complement
of the rotated red and blue edge blocks is injective if the rotated local
\(T\)-region is injective.

The two additional right-collar regions are contiguous \(2\times3\)
rectangles.

Source: arXiv:1804.04964, Section 3, Lemma `lem:injective_union` and proof of
Theorem 3, lines 1322--1500 of `Papers/1804.04964/paper_normal.tex`. -/
theorem verticalComp_injective
    {κ : RegionInjectivityData (SquareLatticeVertex 7 5)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hT : κ.IsInjective (normalSquareVerticalRegionT (width := 7) (height := 5) 0 0)) :
    κ.IsInjective
      (regionComplement
        (squareLatticeContiguousRectangle 2 0 3 2 ∪
          (squareLatticeContiguousRectangle 1 2 2 3 :
            Finset (SquareLatticeVertex 7 5)))) := by
  rw [normalSquareVerticalEdgeComplement_eq_verticalT_union_rightCollar]
  exact hUnion.union_injective
    (hUnion.union_injective hT (h.rect23_injective (by omega) (by omega)))
    (h.rect23_injective (by omega) (by omega))

end NormalSquareLatticeRectangleInjectivityHypotheses

end PEPS
end TNLean

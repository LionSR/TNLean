import TNLean.PEPS.NormalEdgeBlockingCoordinate

/-!
# Translated edge blockings in the normal PEPS proof

This file records the coordinate-origin-parametric horizontal and vertical
edge-blocking pictures used after the normalized one-edge constructions.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, Theorem 3]
-/

namespace TNLean
namespace PEPS

/-! ### Translated horizontal edge blockings -/

/-- A translated horizontal edge in the coordinate frame of the normal
edge-blocking picture.

For `xStart = 0` and `yStart = 0`, this has the same endpoint coordinates as
`normalSquareHorizontalEdge`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500,
where the horizontal edge-blocking picture is translated around the finite
square lattice. -/
def normalSquareHorizontalTranslatedEdge {width height : ℕ} (xStart yStart : ℕ)
    (hx : xStart + 3 ≤ width) (hy : yStart + 3 ≤ height) :
    Edge (squareLatticeGraph width height) where
  val :=
    (((⟨xStart + 1, by omega⟩ : Fin width), (⟨yStart + 2, by omega⟩ : Fin height)),
      ((⟨xStart + 2, by omega⟩ : Fin width), (⟨yStart + 2, by omega⟩ : Fin height)))
  property := by
    constructor
    · change toLex
        (((⟨xStart + 1, by omega⟩ : Fin width),
          (⟨yStart + 2, by omega⟩ : Fin height)) :
            SquareLatticeVertex width height) <
        toLex (((⟨xStart + 2, by omega⟩ : Fin width),
          (⟨yStart + 2, by omega⟩ : Fin height)) :
            SquareLatticeVertex width height)
      rw [Prod.Lex.toLex_lt_toLex]
      simp
    · exact Or.inl ⟨rfl, Or.inl (by simp)⟩

/-- The red block around a translated horizontal edge. -/
abbrev normalSquareHorizontalTranslatedEdgeRed {width height : ℕ}
    (xStart yStart : ℕ) : Finset (SquareLatticeVertex width height) :=
  normalSquareRegionTVerticalBlock xStart yStart

/-- The blue block around a translated horizontal edge. -/
abbrev normalSquareHorizontalTranslatedEdgeBlue {width height : ℕ}
    (xStart yStart : ℕ) : Finset (SquareLatticeVertex width height) :=
  normalSquareRegionTHorizontalBlock xStart yStart

/-- The complementary block around a translated horizontal edge. -/
abbrev normalSquareHorizontalTranslatedEdgeComplement {width height : ℕ}
    (xStart yStart : ℕ) : Finset (SquareLatticeVertex width height) :=
  normalSquareEdgeComplementRegion xStart yStart

/-- A translated horizontal edge is horizontal in the square-lattice graph.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem normalSquareHorizontalTranslatedEdge_isHorizontal {width height : ℕ}
    {xStart yStart : ℕ} (hx : xStart + 3 ≤ width) (hy : yStart + 3 ≤ height) :
    IsHorizontalSquareLatticeEdge
      (normalSquareHorizontalTranslatedEdge xStart yStart hx hy) := by
  change squareLatticeHorizontalNeighbor
    (normalSquareHorizontalTranslatedEdge xStart yStart hx hy).1.1
    (normalSquareHorizontalTranslatedEdge xStart yStart hx hy).1.2
  simp [normalSquareHorizontalTranslatedEdge, squareLatticeHorizontalNeighbor]

/-- A translated horizontal edge has red/blue/complement blocking data once
the translated complementary block is known to be injective.

This is the coordinate-local form of the horizontal edge blocking before a
global choice of translated windows around every edge is made.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def normalSquareHorizontalTranslatedEdge_blockingDatum
    {width height : ℕ} {κ : RegionInjectivityData (SquareLatticeVertex width height)}
    {xStart yStart : ℕ}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hx : xStart + 5 ≤ width) (hy : yStart + 5 ≤ height)
    (hComplement :
      κ.IsInjective (normalSquareHorizontalTranslatedEdgeComplement xStart yStart)) :
    NormalEdgeBlockingData κ (squareLatticeGraph width height)
      (normalSquareHorizontalTranslatedEdge xStart yStart (by omega) (by omega)) where
  red := normalSquareHorizontalTranslatedEdgeRed xStart yStart
  blue := normalSquareHorizontalTranslatedEdgeBlue xStart yStart
  complement := normalSquareHorizontalTranslatedEdgeComplement xStart yStart
  left_mem_red := by
    simp [normalSquareHorizontalTranslatedEdge, normalSquareHorizontalTranslatedEdgeRed,
      normalSquareRegionTVerticalBlock]
  right_mem_blue := by
    simp [normalSquareHorizontalTranslatedEdge, normalSquareHorizontalTranslatedEdgeBlue,
      normalSquareRegionTHorizontalBlock]
  red_injective := h.tVerticalBlock_injective hx hy
  blue_injective := h.tHorizontalBlock_injective hx hy
  complement_injective := hComplement
  red_disjoint_blue := normalSquareRegionTVerticalBlock_disjoint_horizontalBlock xStart yStart
  red_disjoint_complement := by
    rw [Finset.disjoint_left]
    intro v hvRed hvComplement
    rw [mem_normalSquareEdgeComplementRegion] at hvComplement
    exact hvComplement (by simp [normalSquareRegionTHole, hvRed])
  blue_disjoint_complement := by
    rw [Finset.disjoint_left]
    intro v hvBlue hvComplement
    rw [mem_normalSquareEdgeComplementRegion] at hvComplement
    exact hvComplement (by simp [normalSquareRegionTHole, hvBlue])
  cover_univ := by
    have hCover :=
      normalSquareEdgeComplementRegion_union_verticalBlock_union_horizontalBlock
        (width := width) (height := height) xStart yStart
    simpa [normalSquareHorizontalTranslatedEdgeRed, normalSquareHorizontalTranslatedEdgeBlue,
      normalSquareHorizontalTranslatedEdgeComplement, Finset.union_assoc,
      Finset.union_left_comm, Finset.union_comm] using hCover

/-- A translated horizontal edge has red/blue/complement blocking data once
the translated complementary block has a rectangular cover.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def normalSquareHorizontalTranslatedEdge_blockingDatum_of_complementCover
    {width height : ℕ} {κ : RegionInjectivityData (SquareLatticeVertex width height)}
    {xStart yStart : ℕ}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hx : xStart + 5 ≤ width) (hy : yStart + 5 ≤ height)
    (cover : NormalSquareEdgeComplementRectangleCover
      (width := width) (height := height) xStart yStart) :
    NormalEdgeBlockingData κ (squareLatticeGraph width height)
      (normalSquareHorizontalTranslatedEdge xStart yStart (by omega) (by omega)) :=
  normalSquareHorizontalTranslatedEdge_blockingDatum h hx hy
    (h.edgeComplement_injective hUnion cover)

/-- The origin of the translated horizontal picture is the normalized
horizontal edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500,
where the normalized horizontal edge-blocking picture is translated around
the finite square lattice. -/
theorem horizontalTranslatedEdge_zero :
    normalSquareHorizontalTranslatedEdge (width := 5) (height := 7) 0 0
      (by decide) (by decide) = normalSquareHorizontalEdge := by
  ext <;> simp [normalSquareHorizontalTranslatedEdge, normalSquareHorizontalEdge]

/-- The origin of the translated horizontal red block is the normalized red
block.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem horizontalTranslatedRed_zero :
    (normalSquareHorizontalTranslatedEdgeRed (width := 5) (height := 7) 0 0) =
      normalSquareHorizontalEdgeRed := by
  rfl

/-- The origin of the translated horizontal blue block is the normalized blue
block.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem horizontalTranslatedBlue_zero :
    (normalSquareHorizontalTranslatedEdgeBlue (width := 5) (height := 7) 0 0) =
      normalSquareHorizontalEdgeBlue := by
  rfl

/-- The origin of the translated horizontal complementary block is the
normalized complementary block.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem horizontalTranslatedComp_zero :
    (normalSquareHorizontalTranslatedEdgeComplement (width := 5) (height := 7) 0 0) =
      normalSquareHorizontalEdgeComplement := by
  rfl

/-! ### Translated vertical edge blockings -/

/-- A translated vertical edge in the coordinate frame of the normal
edge-blocking picture.

For `xStart = 0` and `yStart = 0`, this has the same endpoint coordinates as
`normalSquareVerticalEdge`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500,
where the vertical edge-blocking picture is translated around the finite
square lattice. -/
def normalSquareVerticalTranslatedEdge {width height : ℕ} (xStart yStart : ℕ)
    (hx : xStart + 3 ≤ width) (hy : yStart + 3 ≤ height) :
    Edge (squareLatticeGraph width height) where
  val :=
    (((⟨xStart + 2, by omega⟩ : Fin width), (⟨yStart + 1, by omega⟩ : Fin height)),
      ((⟨xStart + 2, by omega⟩ : Fin width), (⟨yStart + 2, by omega⟩ : Fin height)))
  property := by
    constructor
    · change toLex
        (((⟨xStart + 2, by omega⟩ : Fin width),
          (⟨yStart + 1, by omega⟩ : Fin height)) :
            SquareLatticeVertex width height) <
        toLex (((⟨xStart + 2, by omega⟩ : Fin width),
          (⟨yStart + 2, by omega⟩ : Fin height)) :
            SquareLatticeVertex width height)
      rw [Prod.Lex.toLex_lt_toLex]
      exact Or.inr ⟨rfl, by simp⟩
    · exact Or.inr ⟨rfl, Or.inl (by simp)⟩

/-- The red block around a translated vertical edge. -/
abbrev normalSquareVerticalTranslatedEdgeRed {width height : ℕ}
    (xStart yStart : ℕ) : Finset (SquareLatticeVertex width height) :=
  squareLatticeContiguousRectangle (xStart + 2) yStart 3 2

/-- The blue block around a translated vertical edge. -/
abbrev normalSquareVerticalTranslatedEdgeBlue {width height : ℕ}
    (xStart yStart : ℕ) : Finset (SquareLatticeVertex width height) :=
  squareLatticeContiguousRectangle (xStart + 1) (yStart + 2) 2 3

/-- The complementary block around a translated vertical edge. -/
abbrev normalSquareVerticalTranslatedEdgeComplement {width height : ℕ}
    (xStart yStart : ℕ) : Finset (SquareLatticeVertex width height) :=
  regionComplement
    (normalSquareVerticalTranslatedEdgeRed xStart yStart ∪
      normalSquareVerticalTranslatedEdgeBlue xStart yStart)

/-- A translated vertical edge is vertical in the square-lattice graph.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem normalSquareVerticalTranslatedEdge_isVertical {width height : ℕ}
    {xStart yStart : ℕ} (hx : xStart + 3 ≤ width) (hy : yStart + 3 ≤ height) :
    IsVerticalSquareLatticeEdge
      (normalSquareVerticalTranslatedEdge xStart yStart hx hy) := by
  change squareLatticeVerticalNeighbor
    (normalSquareVerticalTranslatedEdge xStart yStart hx hy).1.1
    (normalSquareVerticalTranslatedEdge xStart yStart hx hy).1.2
  simp [normalSquareVerticalTranslatedEdge, squareLatticeVerticalNeighbor]

/-- A translated vertical edge has red/blue/complement blocking data once the
translated complementary block is known to be injective.

This is the coordinate-local vertical counterpart of
`normalSquareHorizontalTranslatedEdge_blockingDatum`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def normalSquareVerticalTranslatedEdge_blockingDatum
    {width height : ℕ} {κ : RegionInjectivityData (SquareLatticeVertex width height)}
    {xStart yStart : ℕ}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hx : xStart + 5 ≤ width) (hy : yStart + 5 ≤ height)
    (hComplement :
      κ.IsInjective (normalSquareVerticalTranslatedEdgeComplement xStart yStart)) :
    NormalEdgeBlockingData κ (squareLatticeGraph width height)
      (normalSquareVerticalTranslatedEdge xStart yStart (by omega) (by omega)) where
  red := normalSquareVerticalTranslatedEdgeRed xStart yStart
  blue := normalSquareVerticalTranslatedEdgeBlue xStart yStart
  complement := normalSquareVerticalTranslatedEdgeComplement xStart yStart
  left_mem_red := by
    simp [normalSquareVerticalTranslatedEdge, normalSquareVerticalTranslatedEdgeRed]
  right_mem_blue := by
    simp [normalSquareVerticalTranslatedEdge, normalSquareVerticalTranslatedEdgeBlue]
  red_injective := h.rect32_injective (by omega) (by omega)
  blue_injective := h.rect23_injective (by omega) (by omega)
  complement_injective := hComplement
  red_disjoint_blue := by
    rw [Finset.disjoint_left]
    intro v hvRed hvBlue
    rw [mem_squareLatticeContiguousRectangle] at hvRed hvBlue
    omega
  red_disjoint_complement := by
    rw [Finset.disjoint_left]
    intro v hvRed hvComplement
    rw [mem_regionComplement] at hvComplement
    exact hvComplement (Finset.mem_union.mpr (Or.inl hvRed))
  blue_disjoint_complement := by
    rw [Finset.disjoint_left]
    intro v hvBlue hvComplement
    rw [mem_regionComplement] at hvComplement
    exact hvComplement (Finset.mem_union.mpr (Or.inr hvBlue))
  cover_univ := by
    ext v
    simp [normalSquareVerticalTranslatedEdgeComplement, regionComplement]

/-- A translated vertical edge has red/blue/complement blocking data once the
translated complementary block has a rectangular cover.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def normalSquareVerticalTranslatedEdge_blockingDatum_of_complementCover
    {width height : ℕ} {κ : RegionInjectivityData (SquareLatticeVertex width height)}
    {xStart yStart : ℕ}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hx : xStart + 5 ≤ width) (hy : yStart + 5 ≤ height)
    (cover : SquareLatticeRectangleCover
      (normalSquareVerticalTranslatedEdgeComplement
        (width := width) (height := height) xStart yStart)) :
    NormalEdgeBlockingData κ (squareLatticeGraph width height)
      (normalSquareVerticalTranslatedEdge xStart yStart (by omega) (by omega)) :=
  normalSquareVerticalTranslatedEdge_blockingDatum h hx hy
    (h.injective_of_rectangleCover hUnion cover)

/-- The origin of the translated vertical picture is the normalized vertical
edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500,
where the normalized vertical edge-blocking picture is translated around the
finite square lattice. -/
theorem verticalTranslatedEdge_zero :
    normalSquareVerticalTranslatedEdge (width := 7) (height := 5) 0 0
      (by decide) (by decide) = normalSquareVerticalEdge := by
  ext <;> simp [normalSquareVerticalTranslatedEdge, normalSquareVerticalEdge]

/-- The origin of the translated vertical red block is the normalized red
block.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem verticalTranslatedRed_zero :
    (normalSquareVerticalTranslatedEdgeRed (width := 7) (height := 5) 0 0) =
      normalSquareVerticalEdgeRed := by
  rfl

/-- The origin of the translated vertical blue block is the normalized blue
block.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem verticalTranslatedBlue_zero :
    (normalSquareVerticalTranslatedEdgeBlue (width := 7) (height := 5) 0 0) =
      normalSquareVerticalEdgeBlue := by
  rfl

/-- The origin of the translated vertical complementary block is the normalized
complementary block.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem verticalTranslatedComp_zero :
    (normalSquareVerticalTranslatedEdgeComplement (width := 7) (height := 5) 0 0) =
      normalSquareVerticalEdgeComplement := by
  rfl

end PEPS
end TNLean

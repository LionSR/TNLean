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

/-- The translated horizontal edge is the coordinate right edge at the
corresponding lattice position.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem normalSquareHorizontalTranslatedEdge_eq_rightEdge {width height : ℕ}
    {xStart yStart : ℕ} (hx : xStart + 3 ≤ width) (hy : yStart + 3 ≤ height) :
    normalSquareHorizontalTranslatedEdge xStart yStart hx hy =
      squareLatticeRightEdge (xStart + 1) (yStart + 2) (by omega) (by omega) := by
  rfl

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

/-- A translated horizontal edge supplies the three injective regions used in
the edge-blocked three-site chain.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem normalSquareHorizontalTranslatedEdge_injective_chain
    {width height : ℕ} {κ : RegionInjectivityData (SquareLatticeVertex width height)}
    {xStart yStart : ℕ}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hx : xStart + 5 ≤ width) (hy : yStart + 5 ≤ height)
    (hComplement :
      κ.IsInjective (normalSquareHorizontalTranslatedEdgeComplement xStart yStart)) :
    κ.IsInjective (normalSquareHorizontalTranslatedEdgeRed xStart yStart) ∧
      κ.IsInjective (normalSquareHorizontalTranslatedEdgeBlue xStart yStart) ∧
      κ.IsInjective (normalSquareHorizontalTranslatedEdgeComplement xStart yStart) :=
  (normalSquareHorizontalTranslatedEdge_blockingDatum h hx hy hComplement).injective_chain

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

/-- A translated horizontal edge supplies the three injective regions once the
translated complementary block has a rectangular cover.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem normalSquareHorizontalTranslatedEdge_injective_chain_of_complementCover
    {width height : ℕ} {κ : RegionInjectivityData (SquareLatticeVertex width height)}
    {xStart yStart : ℕ}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hx : xStart + 5 ≤ width) (hy : yStart + 5 ≤ height)
    (cover : NormalSquareEdgeComplementRectangleCover
      (width := width) (height := height) xStart yStart) :
    κ.IsInjective (normalSquareHorizontalTranslatedEdgeRed xStart yStart) ∧
      κ.IsInjective (normalSquareHorizontalTranslatedEdgeBlue xStart yStart) ∧
      κ.IsInjective (normalSquareHorizontalTranslatedEdgeComplement xStart yStart) :=
  (normalSquareHorizontalTranslatedEdge_blockingDatum_of_complementCover
    h hUnion hx hy cover).injective_chain

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

/-- The translated vertical edge is the coordinate upward edge at the
corresponding lattice position.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem normalSquareVerticalTranslatedEdge_eq_upEdge {width height : ℕ}
    {xStart yStart : ℕ} (hx : xStart + 3 ≤ width) (hy : yStart + 3 ≤ height) :
    normalSquareVerticalTranslatedEdge xStart yStart hx hy =
      squareLatticeUpEdge (xStart + 2) (yStart + 1) (by omega) (by omega) := by
  rfl

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

/-- A translated vertical edge supplies the three injective regions used in the
edge-blocked three-site chain.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem normalSquareVerticalTranslatedEdge_injective_chain
    {width height : ℕ} {κ : RegionInjectivityData (SquareLatticeVertex width height)}
    {xStart yStart : ℕ}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hx : xStart + 5 ≤ width) (hy : yStart + 5 ≤ height)
    (hComplement :
      κ.IsInjective (normalSquareVerticalTranslatedEdgeComplement xStart yStart)) :
    κ.IsInjective (normalSquareVerticalTranslatedEdgeRed xStart yStart) ∧
      κ.IsInjective (normalSquareVerticalTranslatedEdgeBlue xStart yStart) ∧
      κ.IsInjective (normalSquareVerticalTranslatedEdgeComplement xStart yStart) :=
  (normalSquareVerticalTranslatedEdge_blockingDatum h hx hy hComplement).injective_chain

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

/-- A translated vertical edge supplies the three injective regions once the
translated complementary block has a rectangular cover.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem normalSquareVerticalTranslatedEdge_injective_chain_of_complementCover
    {width height : ℕ} {κ : RegionInjectivityData (SquareLatticeVertex width height)}
    {xStart yStart : ℕ}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hx : xStart + 5 ≤ width) (hy : yStart + 5 ≤ height)
    (cover : SquareLatticeRectangleCover
      (normalSquareVerticalTranslatedEdgeComplement
        (width := width) (height := height) xStart yStart)) :
    κ.IsInjective (normalSquareVerticalTranslatedEdgeRed xStart yStart) ∧
      κ.IsInjective (normalSquareVerticalTranslatedEdgeBlue xStart yStart) ∧
      κ.IsInjective (normalSquareVerticalTranslatedEdgeComplement xStart yStart) :=
  (normalSquareVerticalTranslatedEdge_blockingDatum_of_complementCover
    h hUnion hx hy cover).injective_chain

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

/-! ### Edge windows for the every-edge construction -/

universe edgeCoverUniverse

/-- A proof that an edge is realized by one of the translated normal
edge-blocking windows.

The constructors deliberately record the rectangular cover of the complementary
region. The remaining finite-geometry step in the source proof is to provide
such a window for every edge of the \(7\times7\) square-lattice PEPS.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
inductive NormalSquareTranslatedEdgeWindow {width height : ℕ}
    (e : Edge (squareLatticeGraph width height)) : Type (edgeCoverUniverse + 1)
  | horizontal (xStart yStart : ℕ)
      (hx : xStart + 5 ≤ width) (hy : yStart + 5 ≤ height)
      (edge_eq :
        normalSquareHorizontalTranslatedEdge xStart yStart (by omega) (by omega) = e)
      (cover : NormalSquareEdgeComplementRectangleCover.{edgeCoverUniverse}
        (width := width) (height := height) xStart yStart)
  | vertical (xStart yStart : ℕ)
      (hx : xStart + 5 ≤ width) (hy : yStart + 5 ≤ height)
      (edge_eq :
        normalSquareVerticalTranslatedEdge xStart yStart (by omega) (by omega) = e)
      (cover : SquareLatticeRectangleCover.{edgeCoverUniverse}
        (normalSquareVerticalTranslatedEdgeComplement
          (width := width) (height := height) xStart yStart))

namespace NormalSquareTranslatedEdgeWindow

/-- A translated edge window gives the one-edge blocking datum for its edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def blockingDatum
    {width height : ℕ} {κ : RegionInjectivityData (SquareLatticeVertex width height)}
    {e : Edge (squareLatticeGraph width height)}
    (w : NormalSquareTranslatedEdgeWindow e)
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ) :
    NormalEdgeBlockingData κ (squareLatticeGraph width height) e :=
  match w with
  | horizontal _xStart _yStart hx hy edge_eq cover =>
      edge_eq ▸
        normalSquareHorizontalTranslatedEdge_blockingDatum_of_complementCover
          h hUnion hx hy cover
  | vertical _xStart _yStart hx hy edge_eq cover =>
      edge_eq ▸
        normalSquareVerticalTranslatedEdge_blockingDatum_of_complementCover
          h hUnion hx hy cover

/-- A translated edge window supplies the three injective regions for its
edge-blocked chain.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem injective_chain
    {width height : ℕ} {κ : RegionInjectivityData (SquareLatticeVertex width height)}
    {e : Edge (squareLatticeGraph width height)}
    (w : NormalSquareTranslatedEdgeWindow e)
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ) :
    κ.IsInjective ((w.blockingDatum h hUnion).red) ∧
      κ.IsInjective ((w.blockingDatum h hUnion).blue) ∧
      κ.IsInjective ((w.blockingDatum h hUnion).complement) :=
  (w.blockingDatum h hUnion).injective_chain

end NormalSquareTranslatedEdgeWindow

/-- A translated horizontal window around a coordinate right edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def normalSquareHorizontalTranslatedEdgeWindow
    {width height : ℕ} (xStart yStart : ℕ)
    (hx : xStart + 5 ≤ width) (hy : yStart + 5 ≤ height)
    (cover : NormalSquareEdgeComplementRectangleCover
      (width := width) (height := height) xStart yStart) :
    NormalSquareTranslatedEdgeWindow
      (squareLatticeRightEdge (width := width) (height := height)
        (xStart + 1) (yStart + 2) (by omega) (by omega)) :=
  NormalSquareTranslatedEdgeWindow.horizontal xStart yStart hx hy
    (normalSquareHorizontalTranslatedEdge_eq_rightEdge (by omega) (by omega)) cover

/-- A translated vertical window around a coordinate upward edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def normalSquareVerticalTranslatedEdgeWindow
    {width height : ℕ} (xStart yStart : ℕ)
    (hx : xStart + 5 ≤ width) (hy : yStart + 5 ≤ height)
    (cover : SquareLatticeRectangleCover
      (normalSquareVerticalTranslatedEdgeComplement
        (width := width) (height := height) xStart yStart)) :
    NormalSquareTranslatedEdgeWindow
      (squareLatticeUpEdge (width := width) (height := height)
        (xStart + 2) (yStart + 1) (by omega) (by omega)) :=
  NormalSquareTranslatedEdgeWindow.vertical xStart yStart hx hy
    (normalSquareVerticalTranslatedEdge_eq_upEdge (by omega) (by omega)) cover

/-- A coordinate right edge admits the translated horizontal window when the
edge has enough room to place the normalized \(5\times7\) blocking frame around
it.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def squareLatticeRightEdgeWindow
    {width height : ℕ} (x y : ℕ)
    (hxLeft : 1 ≤ x) (hxRight : x + 4 ≤ width)
    (hyBottom : 2 ≤ y) (hyTop : y + 3 ≤ height)
    (cover : NormalSquareEdgeComplementRectangleCover
      (width := width) (height := height) (x - 1) (y - 2)) :
    NormalSquareTranslatedEdgeWindow
      (squareLatticeRightEdge (width := width) (height := height)
        x y (by omega) (by omega)) := by
  convert normalSquareHorizontalTranslatedEdgeWindow (x - 1) (y - 2)
    (by omega) (by omega) cover using 1
  ext <;> simp [squareLatticeRightEdge]
  all_goals omega

/-- A coordinate upward edge admits the translated vertical window when the
edge has enough room to place the normalized \(7\times5\) blocking frame around
it.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def squareLatticeUpEdgeWindow
    {width height : ℕ} (x y : ℕ)
    (hxLeft : 2 ≤ x) (hxRight : x + 3 ≤ width)
    (hyBottom : 1 ≤ y) (hyTop : y + 4 ≤ height)
    (cover : SquareLatticeRectangleCover
      (normalSquareVerticalTranslatedEdgeComplement
        (width := width) (height := height) (x - 2) (y - 1))) :
    NormalSquareTranslatedEdgeWindow
      (squareLatticeUpEdge (width := width) (height := height)
        x y (by omega) (by omega)) := by
  convert normalSquareVerticalTranslatedEdgeWindow (x - 2) (y - 1)
    (by omega) (by omega) cover using 1
  ext <;> simp [squareLatticeUpEdge]
  all_goals omega

/-- A horizontal square-lattice edge admits a translated horizontal window when
its ordered left endpoint has the required margins.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def horizontalSquareLatticeEdgeWindow
    {width height : ℕ} (e : Edge (squareLatticeGraph width height))
    (hEdge : IsHorizontalSquareLatticeEdge e)
    (hxLeft : 1 ≤ e.1.1.1.1) (hxRight : e.1.1.1.1 + 4 ≤ width)
    (hyBottom : 2 ≤ e.1.1.2.1) (hyTop : e.1.1.2.1 + 3 ≤ height)
    (cover : NormalSquareEdgeComplementRectangleCover
      (width := width) (height := height) (e.1.1.1.1 - 1) (e.1.1.2.1 - 2)) :
    NormalSquareTranslatedEdgeWindow e := by
  rw [horizontalSquareLatticeEdge_eq_rightEdge e hEdge]
  exact squareLatticeRightEdgeWindow e.1.1.1.1 e.1.1.2.1
    hxLeft hxRight hyBottom hyTop cover

/-- A vertical square-lattice edge admits a translated vertical window when its
ordered lower endpoint has the required margins.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def verticalSquareLatticeEdgeWindow
    {width height : ℕ} (e : Edge (squareLatticeGraph width height))
    (hEdge : IsVerticalSquareLatticeEdge e)
    (hxLeft : 2 ≤ e.1.1.1.1) (hxRight : e.1.1.1.1 + 3 ≤ width)
    (hyBottom : 1 ≤ e.1.1.2.1) (hyTop : e.1.1.2.1 + 4 ≤ height)
    (cover : SquareLatticeRectangleCover
      (normalSquareVerticalTranslatedEdgeComplement
        (width := width) (height := height) (e.1.1.1.1 - 2) (e.1.1.2.1 - 1))) :
    NormalSquareTranslatedEdgeWindow e := by
  rw [verticalSquareLatticeEdge_eq_upEdge e hEdge]
  exact squareLatticeUpEdgeWindow e.1.1.1.1 e.1.1.2.1
    hxLeft hxRight hyBottom hyTop cover

/-- Per-edge data sufficient to realize a square-lattice edge by a translated
normal edge-blocking window.

This packages the remaining finite-geometry input in the current open
rectangular coordinate model: an edge must be horizontal or vertical, have the
corresponding margins, and have a rectangular cover for its complementary
block.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
inductive NormalSquareEdgeMarginCover {width height : ℕ}
    (e : Edge (squareLatticeGraph width height)) : Type (edgeCoverUniverse + 1)
  | horizontal
      (hEdge : IsHorizontalSquareLatticeEdge e)
      (hxLeft : 1 ≤ e.1.1.1.1) (hxRight : e.1.1.1.1 + 4 ≤ width)
      (hyBottom : 2 ≤ e.1.1.2.1) (hyTop : e.1.1.2.1 + 3 ≤ height)
      (cover : NormalSquareEdgeComplementRectangleCover.{edgeCoverUniverse}
        (width := width) (height := height) (e.1.1.1.1 - 1) (e.1.1.2.1 - 2))
  | vertical
      (hEdge : IsVerticalSquareLatticeEdge e)
      (hxLeft : 2 ≤ e.1.1.1.1) (hxRight : e.1.1.1.1 + 3 ≤ width)
      (hyBottom : 1 ≤ e.1.1.2.1) (hyTop : e.1.1.2.1 + 4 ≤ height)
      (cover : SquareLatticeRectangleCover.{edgeCoverUniverse}
        (normalSquareVerticalTranslatedEdgeComplement
          (width := width) (height := height) (e.1.1.1.1 - 2) (e.1.1.2.1 - 1)))

namespace NormalSquareEdgeMarginCover

/-- The translated edge window obtained from oriented margin-and-cover data.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def window {width height : ℕ} {e : Edge (squareLatticeGraph width height)}
    (d : NormalSquareEdgeMarginCover e) :
    NormalSquareTranslatedEdgeWindow e :=
  match d with
  | horizontal hEdge hxLeft hxRight hyBottom hyTop cover =>
      horizontalSquareLatticeEdgeWindow e hEdge hxLeft hxRight hyBottom hyTop cover
  | vertical hEdge hxLeft hxRight hyBottom hyTop cover =>
      verticalSquareLatticeEdgeWindow e hEdge hxLeft hxRight hyBottom hyTop cover

end NormalSquareEdgeMarginCover

/-- A choice of translated edge window for every edge assembles into the normal
edge-blocking hypotheses.

This is the conditional assembly step preceding the finite \(7\times7\)
geometry argument: it assumes the translated window for each edge rather than
constructing those windows.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def normalSquareTranslatedEdgeBlockingHypotheses_of_windows
    {width height : ℕ} {κ : RegionInjectivityData (SquareLatticeVertex width height)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (windows :
      ∀ e : Edge (squareLatticeGraph width height),
        NormalSquareTranslatedEdgeWindow.{edgeCoverUniverse} e) :
    NormalEdgeBlockingHypotheses κ (squareLatticeGraph width height) :=
  NormalEdgeBlockingHypotheses.ofBlockingData fun e =>
    (windows e).blockingDatum h hUnion

/-- A choice of oriented margin-and-cover data for every edge assembles into
the normal edge-blocking hypotheses.

This is the same conditional assembly as
`normalSquareTranslatedEdgeBlockingHypotheses_of_windows`, with the remaining
finite-geometry input expressed directly on each square-lattice edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def normalSquareEdgeBlockingHypotheses_of_marginCovers
    {width height : ℕ} {κ : RegionInjectivityData (SquareLatticeVertex width height)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (data :
      ∀ e : Edge (squareLatticeGraph width height),
        NormalSquareEdgeMarginCover.{edgeCoverUniverse} e) :
    NormalEdgeBlockingHypotheses κ (squareLatticeGraph width height) :=
  normalSquareTranslatedEdgeBlockingHypotheses_of_windows h hUnion fun e =>
    (data e).window

end PEPS
end TNLean

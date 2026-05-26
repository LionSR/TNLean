import TNLean.PEPS.NormalEdgeComplementCover
import TNLean.PEPS.SquareLatticeGraph

/-!
# Coordinate edge blockings in the normal PEPS proof

This file packages the normalized coordinate edge blocking used in the proof of
the normal square-lattice PEPS theorem.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, Theorem 3]
-/

namespace TNLean
namespace PEPS

/-- The distinguished horizontal edge in the normalized \(5\times7\) frame.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500,
where the proof blocks the tensor network around a horizontal edge. -/
def normalSquareHorizontalEdge : Edge (squareLatticeGraph 5 7) where
  val :=
    (((⟨1, by decide⟩ : Fin 5), (⟨2, by decide⟩ : Fin 7)),
      ((⟨2, by decide⟩ : Fin 5), (⟨2, by decide⟩ : Fin 7)))
  property := by
    constructor
    · change toLex
        (((⟨1, by decide⟩ : Fin 5), (⟨2, by decide⟩ : Fin 7)) :
          SquareLatticeVertex 5 7) <
        toLex (((⟨2, by decide⟩ : Fin 5), (⟨2, by decide⟩ : Fin 7)) :
          SquareLatticeVertex 5 7)
      rw [Prod.Lex.toLex_lt_toLex]
      exact Or.inl (by decide)
    · exact squareLatticeGraph_adj_right (⟨1, by decide⟩ : Fin 5)
        (⟨2, by decide⟩ : Fin 7) (by decide)

/-- The distinguished normalized horizontal edge is horizontal in the
square-lattice graph.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500,
where the edge blocking is applied separately to horizontal and vertical
edges. -/
theorem normalSquareHorizontalEdge_isHorizontal :
    IsHorizontalSquareLatticeEdge normalSquareHorizontalEdge := by
  change squareLatticeHorizontalNeighbor normalSquareHorizontalEdge.1.1
    normalSquareHorizontalEdge.1.2
  simp [normalSquareHorizontalEdge, squareLatticeHorizontalNeighbor]

/-- The red block around the normalized horizontal edge. -/
abbrev normalSquareHorizontalEdgeRed : Finset (SquareLatticeVertex 5 7) :=
  normalSquareRegionTVerticalBlock 0 0

/-- The blue block around the normalized horizontal edge. -/
abbrev normalSquareHorizontalEdgeBlue : Finset (SquareLatticeVertex 5 7) :=
  normalSquareRegionTHorizontalBlock 0 0

/-- The complementary block around the normalized horizontal edge. -/
abbrev normalSquareHorizontalEdgeComplement : Finset (SquareLatticeVertex 5 7) :=
  normalSquareEdgeComplementRegion 0 0

/-- The normalized horizontal edge has the red/blue/complement blocking data
used in the proof of the normal square-lattice theorem.

This definition records the set-theoretic and injectivity data for the concrete
horizontal-edge blocking as one `NormalEdgeBlockingData` value. The remaining
step toward
`NormalEdgeBlockingHypotheses` is to translate this coordinate picture around
every horizontal and vertical edge of the finite square lattice.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def normalSquareHorizontalEdge_blockingDatum
    {κ : RegionInjectivityData (SquareLatticeVertex 5 7)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hT : κ.IsInjective (normalSquareRegionT (width := 5) (height := 7) 0 0)) :
    NormalEdgeBlockingData κ (squareLatticeGraph 5 7) normalSquareHorizontalEdge where
  red := normalSquareHorizontalEdgeRed
  blue := normalSquareHorizontalEdgeBlue
  complement := normalSquareHorizontalEdgeComplement
  left_mem_red := by
    simp [normalSquareHorizontalEdge, normalSquareHorizontalEdgeRed,
      normalSquareRegionTVerticalBlock]
  right_mem_blue := by
    simp [normalSquareHorizontalEdge, normalSquareHorizontalEdgeBlue,
      normalSquareRegionTHorizontalBlock]
  red_injective := h.tVerticalBlock_injective (by omega) (by omega)
  blue_injective := h.tHorizontalBlock_injective (by omega) (by omega)
  complement_injective := h.topCollar_injective hUnion hT
  red_disjoint_blue := normalSquareRegionTVerticalBlock_disjoint_horizontalBlock 0 0
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
        (width := 5) (height := 7) 0 0
    simpa [normalSquareHorizontalEdgeRed, normalSquareHorizontalEdgeBlue,
      normalSquareHorizontalEdgeComplement, Finset.union_assoc, Finset.union_left_comm,
      Finset.union_comm] using hCover

/-- The normalized horizontal edge has the red/blue/complement blocking used in
the proof of the normal square-lattice theorem.

This is the tuple form of `normalSquareHorizontalEdge_blockingDatum`, kept for
downstream arguments that use the individual conclusions directly.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem normalSquareHorizontalEdge_blockingData
    {κ : RegionInjectivityData (SquareLatticeVertex 5 7)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hT : κ.IsInjective (normalSquareRegionT (width := 5) (height := 7) 0 0)) :
    normalSquareHorizontalEdge.1.1 ∈ normalSquareHorizontalEdgeRed ∧
      normalSquareHorizontalEdge.1.2 ∈ normalSquareHorizontalEdgeBlue ∧
      κ.IsInjective normalSquareHorizontalEdgeRed ∧
      κ.IsInjective normalSquareHorizontalEdgeBlue ∧
      κ.IsInjective normalSquareHorizontalEdgeComplement ∧
      Disjoint normalSquareHorizontalEdgeRed normalSquareHorizontalEdgeBlue ∧
      Disjoint normalSquareHorizontalEdgeRed normalSquareHorizontalEdgeComplement ∧
      Disjoint normalSquareHorizontalEdgeBlue normalSquareHorizontalEdgeComplement ∧
      normalSquareHorizontalEdgeRed ∪ normalSquareHorizontalEdgeBlue ∪
          normalSquareHorizontalEdgeComplement =
        (Finset.univ : Finset (SquareLatticeVertex 5 7)) := by
  let d := normalSquareHorizontalEdge_blockingDatum h hUnion hT
  exact ⟨d.left_mem_red, d.right_mem_blue, d.red_injective, d.blue_injective,
    d.complement_injective, d.red_disjoint_blue, d.red_disjoint_complement,
    d.blue_disjoint_complement, d.cover_univ⟩

/-- The normalized horizontal edge supplies the three injective regions used in
the edge-blocked three-site chain.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem normalSquareHorizontalEdge_injective_chain
    {κ : RegionInjectivityData (SquareLatticeVertex 5 7)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hT : κ.IsInjective (normalSquareRegionT (width := 5) (height := 7) 0 0)) :
    κ.IsInjective normalSquareHorizontalEdgeRed ∧
      κ.IsInjective normalSquareHorizontalEdgeBlue ∧
      κ.IsInjective normalSquareHorizontalEdgeComplement :=
  (normalSquareHorizontalEdge_blockingDatum h hUnion hT).injective_chain

/-- The normalized horizontal edge has red/blue/complement blocking data once
the local \(T\)-region has a rectangular cover.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1500. -/
def normalSquareHorizontalEdge_blockingDatum_of_TCover
    {κ : RegionInjectivityData (SquareLatticeVertex 5 7)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (cover : NormalSquareRegionTRectangleCover (width := 5) (height := 7) 0 0) :
    NormalEdgeBlockingData κ (squareLatticeGraph 5 7) normalSquareHorizontalEdge :=
  normalSquareHorizontalEdge_blockingDatum h hUnion
    (h.regionT_injective_of_cover hUnion cover)

/-- The normalized horizontal edge supplies the three injective regions once
the local \(T\)-region has a rectangular cover.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1500. -/
theorem normalSquareHorizontalEdge_injective_chain_of_TCover
    {κ : RegionInjectivityData (SquareLatticeVertex 5 7)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (cover : NormalSquareRegionTRectangleCover (width := 5) (height := 7) 0 0) :
    κ.IsInjective normalSquareHorizontalEdgeRed ∧
      κ.IsInjective normalSquareHorizontalEdgeBlue ∧
      κ.IsInjective normalSquareHorizontalEdgeComplement :=
  (normalSquareHorizontalEdge_blockingDatum_of_TCover h hUnion cover).injective_chain

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

/-- The distinguished vertical edge in the normalized \(7\times5\) frame.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500,
where the proof says that vertical edges use the \(7\times5\) counterpart of
the horizontal-edge blocking. -/
def normalSquareVerticalEdge : Edge (squareLatticeGraph 7 5) where
  val :=
    (((⟨2, by decide⟩ : Fin 7), (⟨1, by decide⟩ : Fin 5)),
      ((⟨2, by decide⟩ : Fin 7), (⟨2, by decide⟩ : Fin 5)))
  property := by
    constructor
    · change toLex
        (((⟨2, by decide⟩ : Fin 7), (⟨1, by decide⟩ : Fin 5)) :
          SquareLatticeVertex 7 5) <
        toLex (((⟨2, by decide⟩ : Fin 7), (⟨2, by decide⟩ : Fin 5)) :
          SquareLatticeVertex 7 5)
      rw [Prod.Lex.toLex_lt_toLex]
      exact Or.inr ⟨rfl, by decide⟩
    · exact squareLatticeGraph_adj_up (⟨2, by decide⟩ : Fin 7)
        (⟨1, by decide⟩ : Fin 5) (by decide)

/-- The distinguished normalized vertical edge is vertical in the
square-lattice graph.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500,
where the edge blocking is applied separately to horizontal and vertical
edges. -/
theorem normalSquareVerticalEdge_isVertical :
    IsVerticalSquareLatticeEdge normalSquareVerticalEdge := by
  change squareLatticeVerticalNeighbor normalSquareVerticalEdge.1.1
    normalSquareVerticalEdge.1.2
  simp [normalSquareVerticalEdge, squareLatticeVerticalNeighbor]

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

/-- The red block around the normalized vertical edge. -/
abbrev normalSquareVerticalEdgeRed : Finset (SquareLatticeVertex 7 5) :=
  squareLatticeContiguousRectangle 2 0 3 2

/-- The blue block around the normalized vertical edge. -/
abbrev normalSquareVerticalEdgeBlue : Finset (SquareLatticeVertex 7 5) :=
  squareLatticeContiguousRectangle 1 2 2 3

/-- The complementary block around the normalized vertical edge. -/
abbrev normalSquareVerticalEdgeComplement : Finset (SquareLatticeVertex 7 5) :=
  regionComplement (normalSquareVerticalEdgeRed ∪ normalSquareVerticalEdgeBlue)

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

/-- The normalized vertical edge has the red/blue/complement blocking datum
used in the proof of the normal square-lattice theorem.

This definition records the set-theoretic data for the vertical-edge blocking.
Injectivity of the complementary block is kept as an explicit hypothesis here;
deriving it from the source rectangular hypotheses is the remaining
finite-geometry step before this can be promoted to an every-edge
`NormalEdgeBlockingHypotheses` construction.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def normalSquareVerticalEdge_blockingDatum
    {κ : RegionInjectivityData (SquareLatticeVertex 7 5)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hComplement : κ.IsInjective normalSquareVerticalEdgeComplement) :
    NormalEdgeBlockingData κ (squareLatticeGraph 7 5) normalSquareVerticalEdge where
  red := normalSquareVerticalEdgeRed
  blue := normalSquareVerticalEdgeBlue
  complement := normalSquareVerticalEdgeComplement
  left_mem_red := by
    simp [normalSquareVerticalEdge, normalSquareVerticalEdgeRed]
  right_mem_blue := by
    simp [normalSquareVerticalEdge, normalSquareVerticalEdgeBlue]
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
    simp [normalSquareVerticalEdgeComplement, regionComplement]

/-- The normalized vertical edge has the red/blue/complement blocking geometry
used in the proof of the normal square-lattice theorem.

This is the tuple form of `normalSquareVerticalEdge_blockingDatum`, kept for
downstream arguments that use the individual conclusions directly.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem normalSquareVerticalEdge_blockingData
    {κ : RegionInjectivityData (SquareLatticeVertex 7 5)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hComplement : κ.IsInjective normalSquareVerticalEdgeComplement) :
    normalSquareVerticalEdge.1.1 ∈ normalSquareVerticalEdgeRed ∧
      normalSquareVerticalEdge.1.2 ∈ normalSquareVerticalEdgeBlue ∧
      κ.IsInjective normalSquareVerticalEdgeRed ∧
      κ.IsInjective normalSquareVerticalEdgeBlue ∧
      κ.IsInjective normalSquareVerticalEdgeComplement ∧
      Disjoint normalSquareVerticalEdgeRed normalSquareVerticalEdgeBlue ∧
      Disjoint normalSquareVerticalEdgeRed normalSquareVerticalEdgeComplement ∧
      Disjoint normalSquareVerticalEdgeBlue normalSquareVerticalEdgeComplement ∧
      normalSquareVerticalEdgeRed ∪ normalSquareVerticalEdgeBlue ∪
          normalSquareVerticalEdgeComplement =
        (Finset.univ : Finset (SquareLatticeVertex 7 5)) := by
  let d := normalSquareVerticalEdge_blockingDatum h hComplement
  exact ⟨d.left_mem_red, d.right_mem_blue, d.red_injective, d.blue_injective,
    d.complement_injective, d.red_disjoint_blue, d.red_disjoint_complement,
    d.blue_disjoint_complement, d.cover_univ⟩

/-- The normalized vertical edge has red/blue/complement blocking data once
the rotated local \(T\)-region is injective.

This discharges the complementary-block input of
`normalSquareVerticalEdge_blockingDatum` using the vertical collar identity.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
def normalSquareVerticalEdge_blockingDatum_of_verticalT
    {κ : RegionInjectivityData (SquareLatticeVertex 7 5)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hT : κ.IsInjective (normalSquareVerticalRegionT (width := 7) (height := 5) 0 0)) :
    NormalEdgeBlockingData κ (squareLatticeGraph 7 5) normalSquareVerticalEdge :=
  normalSquareVerticalEdge_blockingDatum h (h.verticalComp_injective hUnion hT)

/-- The normalized vertical edge has red/blue/complement blocking data once the
rotated local \(T\)-region has a rectangular cover.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1500. -/
def normalSquareVerticalEdge_blockingDatum_of_verticalTCover
    {κ : RegionInjectivityData (SquareLatticeVertex 7 5)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (cover : NormalSquareVerticalRegionTRectangleCover
      (width := 7) (height := 5) 0 0) :
    NormalEdgeBlockingData κ (squareLatticeGraph 7 5) normalSquareVerticalEdge :=
  normalSquareVerticalEdge_blockingDatum h (h.verticalComp_inj_of_cover hUnion cover)

/-- The normalized vertical edge supplies the three injective regions used in
the edge-blocked three-site chain.

The complementary-block injectivity remains an explicit input here; discharging
that input from the rectangular hypotheses is the remaining source-geometry
step.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem normalSquareVerticalEdge_injective_chain
    {κ : RegionInjectivityData (SquareLatticeVertex 7 5)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hComplement : κ.IsInjective normalSquareVerticalEdgeComplement) :
    κ.IsInjective normalSquareVerticalEdgeRed ∧
      κ.IsInjective normalSquareVerticalEdgeBlue ∧
      κ.IsInjective normalSquareVerticalEdgeComplement :=
  (normalSquareVerticalEdge_blockingDatum h hComplement).injective_chain

/-- The normalized vertical edge supplies the three injective regions once the
rotated local \(T\)-region is injective.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
theorem normalSquareVerticalEdge_injective_chain_of_verticalT
    {κ : RegionInjectivityData (SquareLatticeVertex 7 5)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hT : κ.IsInjective (normalSquareVerticalRegionT (width := 7) (height := 5) 0 0)) :
    κ.IsInjective normalSquareVerticalEdgeRed ∧
      κ.IsInjective normalSquareVerticalEdgeBlue ∧
      κ.IsInjective normalSquareVerticalEdgeComplement :=
  (normalSquareVerticalEdge_blockingDatum_of_verticalT h hUnion hT).injective_chain

/-- The normalized vertical edge supplies the three injective regions once the
rotated local \(T\)-region has a rectangular cover.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1430--1500. -/
theorem normalSquareVerticalEdge_injective_chain_of_verticalTCover
    {κ : RegionInjectivityData (SquareLatticeVertex 7 5)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (cover : NormalSquareVerticalRegionTRectangleCover
      (width := 7) (height := 5) 0 0) :
    κ.IsInjective normalSquareVerticalEdgeRed ∧
      κ.IsInjective normalSquareVerticalEdgeBlue ∧
      κ.IsInjective normalSquareVerticalEdgeComplement :=
  (normalSquareVerticalEdge_blockingDatum_of_verticalTCover h hUnion cover).injective_chain

end PEPS
end TNLean

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

/-- The red block around the normalized horizontal edge. -/
abbrev normalSquareHorizontalEdgeRed : Finset (SquareLatticeVertex 5 7) :=
  normalSquareRegionTVerticalBlock 0 0

/-- The blue block around the normalized horizontal edge. -/
abbrev normalSquareHorizontalEdgeBlue : Finset (SquareLatticeVertex 5 7) :=
  normalSquareRegionTHorizontalBlock 0 0

/-- The complementary block around the normalized horizontal edge. -/
abbrev normalSquareHorizontalEdgeComplement : Finset (SquareLatticeVertex 5 7) :=
  normalSquareEdgeComplementRegion 0 0

/-- The normalized horizontal edge has the red/blue/complement blocking used in
the proof of the normal square-lattice theorem.

This theorem records the set-theoretic and injectivity data for the concrete
horizontal-edge blocking. The remaining step toward
`NormalEdgeBlockingHypotheses` is to translate this coordinate picture around
every horizontal and vertical edge of the finite square lattice.

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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [normalSquareHorizontalEdge, normalSquareHorizontalEdgeRed,
      normalSquareRegionTVerticalBlock]
  · simp [normalSquareHorizontalEdge, normalSquareHorizontalEdgeBlue,
      normalSquareRegionTHorizontalBlock]
  · exact h.tVerticalBlock_injective (by omega) (by omega)
  · exact h.tHorizontalBlock_injective (by omega) (by omega)
  · exact h.topCollar_injective hUnion hT
  · exact normalSquareRegionTVerticalBlock_disjoint_horizontalBlock 0 0
  · rw [Finset.disjoint_left]
    intro v hvRed hvComplement
    rw [mem_normalSquareEdgeComplementRegion] at hvComplement
    exact hvComplement (by simp [normalSquareRegionTHole, hvRed])
  · rw [Finset.disjoint_left]
    intro v hvBlue hvComplement
    rw [mem_normalSquareEdgeComplementRegion] at hvComplement
    exact hvComplement (by simp [normalSquareRegionTHole, hvBlue])
  · have hCover :=
      normalSquareEdgeComplementRegion_union_verticalBlock_union_horizontalBlock
        (width := 5) (height := 7) 0 0
    simpa [normalSquareHorizontalEdgeRed, normalSquareHorizontalEdgeBlue,
      normalSquareHorizontalEdgeComplement, Finset.union_assoc, Finset.union_left_comm,
      Finset.union_comm] using hCover

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

/-- The red block around the normalized vertical edge. -/
abbrev normalSquareVerticalEdgeRed : Finset (SquareLatticeVertex 7 5) :=
  squareLatticeContiguousRectangle 2 0 3 2

/-- The blue block around the normalized vertical edge. -/
abbrev normalSquareVerticalEdgeBlue : Finset (SquareLatticeVertex 7 5) :=
  squareLatticeContiguousRectangle 1 2 2 3

/-- The complementary block around the normalized vertical edge. -/
abbrev normalSquareVerticalEdgeComplement : Finset (SquareLatticeVertex 7 5) :=
  regionComplement (normalSquareVerticalEdgeRed ∪ normalSquareVerticalEdgeBlue)

/-- The normalized vertical edge has the red/blue/complement blocking geometry
used in the proof of the normal square-lattice theorem.

This theorem records the set-theoretic data for the vertical-edge blocking.
Injectivity of the complementary block is kept as an explicit hypothesis here;
deriving it from the source rectangular hypotheses is the remaining
finite-geometry step before this can be promoted to an every-edge
`NormalEdgeBlockingHypotheses` construction.

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
  refine ⟨?_, ?_, ?_, ?_, hComplement, ?_, ?_, ?_, ?_⟩
  · simp [normalSquareVerticalEdge, normalSquareVerticalEdgeRed]
  · simp [normalSquareVerticalEdge, normalSquareVerticalEdgeBlue]
  · exact h.rect32_injective (by omega) (by omega)
  · exact h.rect23_injective (by omega) (by omega)
  · rw [Finset.disjoint_left]
    intro v hvRed hvBlue
    rw [mem_squareLatticeContiguousRectangle] at hvRed hvBlue
    omega
  · rw [Finset.disjoint_left]
    intro v hvRed hvComplement
    rw [mem_regionComplement] at hvComplement
    exact hvComplement (Finset.mem_union.mpr (Or.inl hvRed))
  · rw [Finset.disjoint_left]
    intro v hvBlue hvComplement
    rw [mem_regionComplement] at hvComplement
    exact hvComplement (Finset.mem_union.mpr (Or.inr hvBlue))
  · ext v
    simp [normalSquareVerticalEdgeComplement, regionComplement]

end PEPS
end TNLean

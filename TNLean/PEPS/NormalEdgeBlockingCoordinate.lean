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

end PEPS
end TNLean

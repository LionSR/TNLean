import TNLean.PEPS.NormalEdgeBlockingTranslated

/-!
# Square-lattice normal PEPS blocking hypotheses

This file connects the square-lattice edge-blocking construction with the
general normal PEPS blocking hypotheses.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, Theorem 3]
-/

namespace TNLean
namespace PEPS

universe edgeCoverUniverse

/-- Oriented margin-and-cover hypotheses at every edge, together with one-site
separation, assemble into the general normal PEPS blocking hypotheses.

The edge-blocking part is the existing construction
`normalSquareEdgeBlockingHypotheses_of_marginCovers`; the one-site separation
hypothesis is carried unchanged.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500,
and theorem labelled `normal`, lines 1576--1583. -/
def normalSquarePEPSBlockingHypotheses_of_marginCovers
    {width height : ℕ} {κ : RegionInjectivityData (SquareLatticeVertex width height)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (data :
      ∀ e : Edge (squareLatticeGraph width height),
        NormalSquareEdgeMarginCover.{edgeCoverUniverse} e)
    (oneSite : NormalOneSiteSeparationHypotheses κ) :
    NormalPEPSBlockingHypotheses κ (squareLatticeGraph width height) where
  edgeBlocking := normalSquareEdgeBlockingHypotheses_of_marginCovers h hUnion data
  oneSiteSeparation := oneSite

/-- In the square-lattice construction from margin-and-cover hypotheses, the
edge-blocking hypotheses are exactly the edge-blocking construction from those
hypotheses.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500,
and theorem labelled `normal`, lines 1576--1583. -/
theorem normalSquarePEPSBlockingHypotheses_edgeBlocking_of_marginCovers
    {width height : ℕ} {κ : RegionInjectivityData (SquareLatticeVertex width height)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (data :
      ∀ e : Edge (squareLatticeGraph width height),
        NormalSquareEdgeMarginCover.{edgeCoverUniverse} e)
    (oneSite : NormalOneSiteSeparationHypotheses κ) :
    (normalSquarePEPSBlockingHypotheses_of_marginCovers h hUnion data oneSite).edgeBlocking =
      normalSquareEdgeBlockingHypotheses_of_marginCovers h hUnion data :=
  rfl

/-- The edge datum recovered from the square-lattice construction assembled
from margin-and-cover hypotheses is the datum supplied by the corresponding
edge datum.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500,
and theorem labelled `normal`, lines 1576--1583. -/
theorem normalSquarePEPSBlockingHypotheses_blockingData_of_marginCovers
    {width height : ℕ} {κ : RegionInjectivityData (SquareLatticeVertex width height)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (data :
      ∀ e : Edge (squareLatticeGraph width height),
        NormalSquareEdgeMarginCover.{edgeCoverUniverse} e)
    (oneSite : NormalOneSiteSeparationHypotheses κ)
    (e : Edge (squareLatticeGraph width height)) :
    (normalSquarePEPSBlockingHypotheses_of_marginCovers
      h hUnion data oneSite).edgeBlocking.blockingData e =
      (data e).blockingDatum h hUnion := by
  rfl

/-- In the square-lattice construction from margin-and-cover hypotheses, the
one-site separation hypothesis is the supplied one.

Source: arXiv:1804.04964, Section 3, theorem labelled `normal`,
lines 1576--1583. -/
theorem normalSquarePEPSBlockingHypotheses_oneSiteSeparation_of_marginCovers
    {width height : ℕ} {κ : RegionInjectivityData (SquareLatticeVertex width height)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (data :
      ∀ e : Edge (squareLatticeGraph width height),
        NormalSquareEdgeMarginCover.{edgeCoverUniverse} e)
    (oneSite : NormalOneSiteSeparationHypotheses κ) :
    (normalSquarePEPSBlockingHypotheses_of_marginCovers
      h hUnion data oneSite).oneSiteSeparation = oneSite :=
  rfl

/-- The square-lattice hypotheses assembled from margin-and-cover assumptions
supply the three injective regions around every edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500,
and theorem labelled `normal`, lines 1576--1583. -/
theorem normalSquarePEPSBlockingHypotheses_injective_chain_of_marginCovers
    {width height : ℕ} {κ : RegionInjectivityData (SquareLatticeVertex width height)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (data :
      ∀ e : Edge (squareLatticeGraph width height),
        NormalSquareEdgeMarginCover.{edgeCoverUniverse} e)
    (oneSite : NormalOneSiteSeparationHypotheses κ)
    (e : Edge (squareLatticeGraph width height)) :
    let H := normalSquarePEPSBlockingHypotheses_of_marginCovers h hUnion data oneSite
    κ.IsInjective (H.edgeBlocking.red e) ∧
      κ.IsInjective (H.edgeBlocking.blue e) ∧
      κ.IsInjective (H.edgeBlocking.complement e) :=
  (normalSquarePEPSBlockingHypotheses_of_marginCovers
    h hUnion data oneSite).injective_chain_at_edge e

/-- The square-lattice hypotheses assembled from margin-and-cover assumptions
supply endpoint membership, pairwise disjointness, and coverage around
every edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500,
and theorem labelled `normal`, lines 1576--1583. -/
theorem normalSquarePEPSBlockingHypotheses_endpoint_disjoint_cover_of_marginCovers
    {width height : ℕ} {κ : RegionInjectivityData (SquareLatticeVertex width height)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (data :
      ∀ e : Edge (squareLatticeGraph width height),
        NormalSquareEdgeMarginCover.{edgeCoverUniverse} e)
    (oneSite : NormalOneSiteSeparationHypotheses κ)
    (e : Edge (squareLatticeGraph width height)) :
    let H := normalSquarePEPSBlockingHypotheses_of_marginCovers h hUnion data oneSite
    e.1.1 ∈ H.edgeBlocking.red e ∧ e.1.2 ∈ H.edgeBlocking.blue e ∧
      Disjoint (H.edgeBlocking.red e) (H.edgeBlocking.blue e) ∧
      Disjoint (H.edgeBlocking.red e) (H.edgeBlocking.complement e) ∧
      Disjoint (H.edgeBlocking.blue e) (H.edgeBlocking.complement e) ∧
      H.edgeBlocking.red e ∪ H.edgeBlocking.blue e ∪
          H.edgeBlocking.complement e = Finset.univ :=
  (normalSquarePEPSBlockingHypotheses_of_marginCovers
    h hUnion data oneSite).endpoint_disjoint_cover_at_edge e

/-- The square-lattice hypotheses assembled from margin-and-cover assumptions
inherit the supplied one-site comparison regions.

Source: arXiv:1804.04964, Section 3, theorem labelled `normal`,
lines 1576--1583. -/
theorem normalSquarePEPSBlockingHypotheses_mem_withSite_iff_of_marginCovers
    {width height : ℕ} {κ : RegionInjectivityData (SquareLatticeVertex width height)}
    (h : NormalSquareLatticeRectangleInjectivityHypotheses κ)
    (hUnion : RegionInjectivityUnionClosure κ)
    (data :
      ∀ e : Edge (squareLatticeGraph width height),
        NormalSquareEdgeMarginCover.{edgeCoverUniverse} e)
    (oneSite : NormalOneSiteSeparationHypotheses κ)
    (v w : SquareLatticeVertex width height) :
    let H := normalSquarePEPSBlockingHypotheses_of_marginCovers h hUnion data oneSite
    w ∈ H.oneSiteSeparation.withSite v ↔
      w = v ∨ w ∈ H.oneSiteSeparation.withoutSite v :=
  (normalSquarePEPSBlockingHypotheses_of_marginCovers
    h hUnion data oneSite).mem_withSite_iff v w

end PEPS
end TNLean

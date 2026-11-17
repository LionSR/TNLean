/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RectangularHamiltonian
import TNLean.PEPS.Approximation.Basic
import TNLean.PEPS.Approximation.SquareGridContraction
import TNLean.PEPS.AreaLaw.EdgeCrossingBudget
import TNLean.PEPS.IsoTransport

/-!
# Original interaction supports in the integer rectangle

The bijection from original site and forward-edge labels to rectangle sites
and unordered edges preserves their designated supports. The order chosen
for rectangle sites affects only the representative of each unordered edge.

Source: polynomial-PEPS `00-introduction.tex`, `eq:model`, and
`03-patches.tex`, lines 213–336; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open ManyBody (SquareLatticeSiteOrEdge squareLatticeSiteOrEdgeSupport)

namespace TNLean.PEPS.Approximation

/-- Relabelling the original sites and forward edges gives precisely the
nearest-neighbor supports in the integer rectangle.
Source: polynomial-PEPS `eq:model` and `03-patches.tex`, lines 213–336. -/
theorem rectangleAreaLawSupport_val_eq_nearestNeighborSupport (L : ℕ)
    [LinearOrder (Lattice.Site (AreaLaw.rectangularDomain L L))]
    (i : SquareLatticeSiteOrEdge L L) :
    let e := Equiv.sumCongr (AreaLaw.rectangleSiteEquiv L L)
      (ManyBody.Edge.equiv (AreaLaw.rectangleGraphIso L L))
    (AreaLaw.rectangleAreaLawSupport L L i).val = AreaLaw.nearestNeighborSupport (e i) := by
  rcases i with v | e <;>
    simp only [AreaLaw.rectangleAreaLawSupport, squareLatticeSiteOrEdgeSupport,
      AreaLaw.nearestNeighborSupport, Finset.image_singleton, Finset.image_insert,
      Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr,
      ManyBody.Edge.equiv_apply]
  exact (Finset.coe_injective
    (Finset.coe_pair.trans
      ((Set.pair_eq_pair_iff.mpr
        (ManyBody.Edge.map_endpoints (AreaLaw.rectangleGraphIso L L)
          e)).trans Finset.coe_pair.symm))).symm

end TNLean.PEPS.Approximation

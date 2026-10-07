/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.SideEndpoints
import TNLean.PEPS.AreaLaw.Geometry.ActualSideMatching
import TNLean.PEPS.AreaLaw.Geometry.ElementarySideOpponents
import TNLean.PEPS.AreaLaw.Geometry.CellContacts
import TNLean.PEPS.AreaLaw.Geometry.DummyCorners

/-!
Kernel dependency audit of four new endpoint, matching and opponent-existence results
and five reverified contact/corner declarations.
-/

#print axioms TNLean.PEPS.AreaLaw.Geometry.cellFan_unsplit_endpoints_coordinates
#print axioms TNLean.PEPS.AreaLaw.Geometry.cellFan_unsplit_endpoints_are_corners
#print axioms TNLean.PEPS.AreaLaw.Geometry.fineLayer_elementary_contact_match
#print axioms TNLean.PEPS.AreaLaw.Geometry.exists_elementarySide_opponent
#print axioms TNLean.PEPS.AreaLaw.Geometry.dyadicCellSide
#print axioms TNLean.PEPS.AreaLaw.Geometry.fineLayer_cells_disjoint
#print axioms TNLean.PEPS.AreaLaw.Geometry.fineLayer_closedCell_contact
#print axioms TNLean.PEPS.AreaLaw.Geometry.dyadicNeighborhood_corner_on_side
#print axioms TNLean.PEPS.AreaLaw.Geometry.dyadicNeighborhood_corner_on_elementarySide

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.CellContacts
import TNLean.PEPS.AreaLaw.Geometry.DummyCorners
import TNLean.PEPS.AreaLaw.Geometry.FineCellPartition

/-! Axiom audit of the seven cell-contact, dummy-corner and fine-cell-partition declarations. -/

#print axioms TNLean.PEPS.AreaLaw.Geometry.dyadicCellSide
#print axioms TNLean.PEPS.AreaLaw.Geometry.fineLayer_cells_disjoint
#print axioms TNLean.PEPS.AreaLaw.Geometry.fineLayer_closedCell_contact
#print axioms TNLean.PEPS.AreaLaw.Geometry.dyadicNeighborhood_corner_on_side
#print axioms TNLean.PEPS.AreaLaw.Geometry.dyadicNeighborhood_corner_on_elementarySide
#print axioms TNLean.PEPS.AreaLaw.Geometry.exists_unique_fineCell_of_not_mem_dyadicNeighborhood
#print axioms TNLean.PEPS.AreaLaw.Geometry.dyadicNeighborhood_union_iUnion_fineCells_eq_univ

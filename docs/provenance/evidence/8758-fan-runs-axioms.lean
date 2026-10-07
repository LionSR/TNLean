/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.FanRuns
import TNLean.PEPS.AreaLaw.Geometry.SideSubdivision
import TNLean.PEPS.AreaLaw.Geometry.LayerPartition
import TNLean.PEPS.AreaLaw.Geometry.FineMarkSeparation
import TNLean.PEPS.AreaLaw.Geometry.NonbeltPrimaries

/-! Axiom audit of fourteen new fan-run, corner-subdivision and layer-partition declarations,
and the four prior declarations in the two files whose proofs use their shared cell-containment theorem. -/

#print axioms TNLean.PEPS.AreaLaw.Geometry.cellFanRunGraph
#print axioms TNLean.PEPS.AreaLaw.Geometry.CellFanRun
#print axioms TNLean.PEPS.AreaLaw.Geometry.cellFanRunRegion
#print axioms TNLean.PEPS.AreaLaw.Geometry.cellFanRun_color_eq
#print axioms TNLean.PEPS.AreaLaw.Geometry.cellFanRunRegions_cover
#print axioms TNLean.PEPS.AreaLaw.Geometry.cellFanRun_adjacent_colors_ne
#print axioms TNLean.PEPS.AreaLaw.Geometry.cellFanRun_all_equal
#print axioms TNLean.PEPS.AreaLaw.Geometry.dyadicCellCorner
#print axioms TNLean.PEPS.AreaLaw.Geometry.fineLayer_corner_on_side
#print axioms TNLean.PEPS.AreaLaw.Geometry.dyadicLayer_pairwiseDisjoint
#print axioms TNLean.PEPS.AreaLaw.Geometry.dyadicNeighborhood_disjoint_later_layer
#print axioms TNLean.PEPS.AreaLaw.Geometry.exists_unique_layer_of_not_mem_dyadicNeighborhood
#print axioms TNLean.PEPS.AreaLaw.Geometry.dyadicNeighborhood_union_iUnion_layers_eq_univ

#print axioms TNLean.PEPS.AreaLaw.Geometry.dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices

#print axioms TNLean.PEPS.AreaLaw.Geometry.fineLayer_marks_dist_ge
#print axioms TNLean.PEPS.AreaLaw.Geometry.closure_nonbeltCell_subset_primaryBirthRegion
#print axioms TNLean.PEPS.AreaLaw.Geometry.exists_unique_primary_of_nonbeltCell

#print axioms TNLean.PEPS.AreaLaw.Geometry.nonbeltPitchIndex

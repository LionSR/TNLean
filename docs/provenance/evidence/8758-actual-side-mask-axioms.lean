/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.SideSubdivisionMask
import TNLean.PEPS.AreaLaw.Geometry.DummyContacts

/-! Axiom audit of the eight actual side-mask and dummy-neighborhood declarations. -/

#print axioms TNLean.PEPS.AreaLaw.Geometry.fineLayerSplitMask
#print axioms TNLean.PEPS.AreaLaw.Geometry.fineLayerSplitMask_eq_true_iff
#print axioms TNLean.PEPS.AreaLaw.Geometry.cellFan_elementary_endpoints_cases
#print axioms TNLean.PEPS.AreaLaw.Geometry.cellFan_elementary_segment_subset_whole
#print axioms TNLean.PEPS.AreaLaw.Geometry.fineLayer_corner_on_elementarySide
#print axioms TNLean.PEPS.AreaLaw.Geometry.dyadicNeighborhood_exists_dist_le
#print axioms TNLean.PEPS.AreaLaw.Geometry.dyadicNeighborhood_dist_later_layer
#print axioms TNLean.PEPS.AreaLaw.Geometry.dyadicNeighborhood_contact_layer_eq

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.PrimaryRegions
import TNLean.PEPS.AreaLaw.Geometry.PrimaryFragments
import TNLean.PEPS.AreaLaw.Geometry.AdjacentScales

/-! Axiom audit of the seventeen primary-region and adjacent-scale declarations. -/

#print axioms TNLean.PEPS.AreaLaw.Geometry.pitchInterior
#print axioms TNLean.PEPS.AreaLaw.Geometry.primaryFragment
#print axioms TNLean.PEPS.AreaLaw.Geometry.primaryFragmentIndices
#print axioms TNLean.PEPS.AreaLaw.Geometry.primaryBirthRegion
#print axioms TNLean.PEPS.AreaLaw.Geometry.primaryBirthRegion_subset_closure_pitchInterior
#print axioms TNLean.PEPS.AreaLaw.Geometry.primaryBirthRegion_dist_le
#print axioms TNLean.PEPS.AreaLaw.Geometry.primaryBirthRegion_diam_le
#print axioms TNLean.PEPS.AreaLaw.Geometry.primaryBirthRegion_dist_separation
#print axioms TNLean.PEPS.AreaLaw.Geometry.card_primaryFragmentIndices_le
#print axioms TNLean.PEPS.AreaLaw.Geometry.primaryBirthRegion_eq_iUnion_primaryFragment
#print axioms TNLean.PEPS.AreaLaw.Geometry.primaryFragment_eq_closedRectangle
#print axioms TNLean.PEPS.AreaLaw.Geometry.primaryFragment_subset_closure_dyadicCell
#print axioms TNLean.PEPS.AreaLaw.Geometry.primaryFragment_dist_le
#print axioms TNLean.PEPS.AreaLaw.Geometry.primaryFragment_diam_le
#print axioms TNLean.PEPS.AreaLaw.Geometry.fineScaleIndex_mono
#print axioms TNLean.PEPS.AreaLaw.Geometry.fineScaleIndex_succ
#print axioms TNLean.PEPS.AreaLaw.Geometry.fineScale_side_succ

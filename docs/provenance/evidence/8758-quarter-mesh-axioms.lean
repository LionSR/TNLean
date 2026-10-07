/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.MeshGeometry
import TNLean.PEPS.AreaLaw.Geometry.LocalLayers

/-! Axiom audit of the six affine-mesh and local-layer declarations. -/

#print axioms TNLean.PEPS.AreaLaw.Geometry.affineMesh
#print axioms TNLean.PEPS.AreaLaw.Geometry.beltMarks_subset_affineMesh
#print axioms TNLean.PEPS.AreaLaw.Geometry.affineMesh_dist_ge
#print axioms TNLean.PEPS.AreaLaw.Geometry.affineMesh_line_dist_ge
#print axioms TNLean.PEPS.AreaLaw.Geometry.dyadicLayer_dist_nonadjacent_fineScale
#print axioms TNLean.PEPS.AreaLaw.Geometry.dyadicLayer_nearby_indices

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.BoundaryConventions
import TNLean.PEPS.AreaLaw.VertexBoundaryCorollaries

/-! Dependency audit for the vertex-boundary comparison and conditional entropy bounds. -/

set_option linter.hashCommand false

#print axioms TNLean.PEPS.AreaLaw.innerBoundary
#print axioms TNLean.PEPS.AreaLaw.endpointBoundary
#print axioms TNLean.PEPS.AreaLaw.innerBoundary_empty
#print axioms TNLean.PEPS.AreaLaw.innerBoundary_univ
#print axioms TNLean.PEPS.AreaLaw.endpointBoundary_empty
#print axioms TNLean.PEPS.AreaLaw.endpointBoundary_univ
#print axioms TNLean.PEPS.AreaLaw.domainGraph_degree_le_four
#print axioms TNLean.PEPS.AreaLaw.edgeBoundary_card_le_four_mul_innerBoundary_card
#print axioms TNLean.PEPS.AreaLaw.edgeBoundary_card_le_two_mul_endpointBoundary_card
#print axioms TNLean.PEPS.AreaLaw.regionalEntropy_le_four_mul_innerBoundary_card
#print axioms TNLean.PEPS.AreaLaw.regionalEntropy_le_two_mul_endpointBoundary_card
#print axioms TNLean.PEPS.AreaLaw.UniformAreaLaw.vertex_boundary_bounds

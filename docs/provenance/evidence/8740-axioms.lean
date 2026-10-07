/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceApproximation

/-! # Kernel dependency audit for the square-grid PEPS bridge

Audit every declaration registered in the issue #8740 provenance shard.
-/

set_option linter.hashCommand false

#print axioms TNLean.PEPS.Approximation.Vertex
#print axioms TNLean.PEPS.Approximation.ForwardAdjacent
#print axioms TNLean.PEPS.Approximation.ForwardEdge
#print axioms TNLean.PEPS.Approximation.Pinned.IncidentEdge
#print axioms TNLean.PEPS.Approximation.Pinned.State
#print axioms TNLean.PEPS.Approximation.Pinned.LocalTensor
#print axioms TNLean.PEPS.Approximation.Pinned.contractPEPS
#print axioms TNLean.PEPS.Approximation.Vector.IncidentEdge
#print axioms TNLean.PEPS.Approximation.Vector.State
#print axioms TNLean.PEPS.Approximation.Vector.Tensor
#print axioms TNLean.PEPS.Approximation.Vector.Tensor.contract
#print axioms TNLean.PEPS.Approximation.Vector.Tensor.maxBondDim
#print axioms TNLean.PEPS.Approximation.forwardSquareEdgeEquiv
#print axioms TNLean.PEPS.Approximation.forwardSquareEdgeEquiv_val
#print axioms TNLean.PEPS.Approximation.forwardSquareEdgeEquiv_symm_val
#print axioms TNLean.PEPS.Approximation.forwardSquareIncidentEquiv
#print axioms TNLean.PEPS.Approximation.pinnedSquareIncidentEquiv
#print axioms TNLean.PEPS.Approximation.forwardSquareIncidentEquiv_val
#print axioms TNLean.PEPS.Approximation.pinnedSquareIncidentEquiv_val
#print axioms TNLean.PEPS.Approximation.graphBondDim
#print axioms TNLean.PEPS.Approximation.graphBondDim_forward
#print axioms TNLean.PEPS.Approximation.forwardSquareVirtualConfigEquiv
#print axioms TNLean.PEPS.Approximation.forwardSquareVirtualConfigEquiv_incident
#print axioms TNLean.PEPS.Approximation.forwardSquareVirtualConfigEquiv_pinnedIncident
#print axioms TNLean.PEPS.Approximation.pinnedTensorToGraphTensor
#print axioms TNLean.PEPS.Approximation.vectorTensorToGraphTensor
#print axioms TNLean.PEPS.Approximation.pinnedTensorToGraphTensor_component
#print axioms TNLean.PEPS.Approximation.vectorTensorToGraphTensor_component
#print axioms TNLean.PEPS.Approximation.stateCoeff_pinnedTensorToGraphTensor
#print axioms TNLean.PEPS.Approximation.stateCoeff_vectorTensorToGraphTensor
#print axioms TNLean.PEPS.Approximation.squareGridStateIsometry
#print axioms TNLean.PEPS.Approximation.vector_pinnedTensorToGraphTensor
#print axioms TNLean.PEPS.Approximation.vector_vectorTensorToGraphTensor
#print axioms TNLean.PEPS.Approximation.norm_pinnedTensorToGraphTensor
#print axioms TNLean.PEPS.Approximation.nonzero_pinnedTensorToGraphTensor
#print axioms TNLean.PEPS.Approximation.normalized_error_pinnedTensorToGraphTensor
#print axioms TNLean.PEPS.Approximation.normalized_error_vectorTensorToGraphTensor
#print axioms TNLean.PEPS.Approximation.graphBondDim_forall
#print axioms TNLean.PEPS.Approximation.vectorTensorToGraphTensor_bondDim_pos
#print axioms TNLean.PEPS.Approximation.maxBondDim_le_iff
#print axioms TNLean.PEPS.Approximation.forwardSquareBoundaryEquiv
#print axioms TNLean.PEPS.Approximation.forwardSquareBoundary_card
#print axioms TNLean.PEPS.Approximation.squareComplementConfigEquiv
#print axioms TNLean.PEPS.Approximation.regionReducedDensity_eq_piSubtype
#print axioms TNLean.PEPS.Approximation.regionReducedDensity_pinnedTensorToGraphTensor
#print axioms TNLean.PEPS.Approximation.regionReducedDensity_vectorTensorToGraphTensor
#print axioms TNLean.PEPS.Approximation.entropy_pinnedTensorToGraphTensor
#print axioms TNLean.PEPS.Approximation.entropy_vectorTensorToGraphTensor
#print axioms TNLean.PEPS.Approximation.Pinned.HasPEPSApproximation
#print axioms TNLean.PEPS.Approximation.Vector.PhaseErrorAtMost
#print axioms TNLean.PEPS.Approximation.phaseErrorAtMost_vectorTensorToGraphTensor
#print axioms TNLean.PEPS.Approximation.hasPEPSApproximation_of_pinned
#print axioms TNLean.PEPS.Approximation.hasPEPSApproximation_of_vector
#print axioms TNLean.PEPS.Approximation.Pinned.RegionConfiguration
#print axioms TNLean.PEPS.Approximation.Pinned.joinConfigurations
#print axioms TNLean.PEPS.Approximation.Pinned.coefficientMatrix
#print axioms TNLean.PEPS.Approximation.Pinned.reducedDensity
#print axioms TNLean.PEPS.Approximation.regionReducedDensity_eq_pinnedReducedDensity
#print axioms TNLean.PEPS.Approximation.maxBondDim_real_le_iff
#print axioms TNLean.PEPS.Approximation.hasPEPSApproximation_of_vector_max

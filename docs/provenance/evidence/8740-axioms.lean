/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SquareGridContraction

/-! # Kernel audit of the standalone square-grid contraction bridge -/

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

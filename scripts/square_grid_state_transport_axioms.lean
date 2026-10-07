/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SquareGridBounds
import TNLean.PEPS.Approximation.RegionalStates

/-! # Kernel dependency report for the square-grid state comparison -/

-- These reports are the output consumed by the declaration provenance audit.
set_option linter.hashCommand false

#print axioms TNLean.PEPS.Approximation.stateVector_pinnedTensorToGraphTensor
#print axioms TNLean.PEPS.Approximation.stateVector_vectorTensorToGraphTensor
#print axioms TNLean.PEPS.Approximation.isometry_squareGridState
#print axioms TNLean.PEPS.Approximation.Vector.PhaseErrorAtMost
#print axioms TNLean.PEPS.Approximation.phaseErrorAtMost_vectorTensorToGraphTensor
#print axioms TNLean.PEPS.Approximation.Vector.Tensor.maxBondDim_le_iff
#print axioms TNLean.PEPS.Approximation.vectorTensorToGraphTensor_bondDim
#print axioms TNLean.PEPS.Approximation.maxBondDim_vectorTensorToGraphTensor
#print axioms TNLean.PEPS.Approximation.pinnedTensorToGraphTensor_bond_bounds
#print axioms TNLean.PEPS.Approximation.norm_stateVector_pinnedTensorToGraphTensor
#print axioms TNLean.PEPS.Approximation.pinnedTensorToGraphTensor_normalized
#print axioms TNLean.PEPS.Approximation.pinnedTensorToGraphTensor_approximation
#print axioms TNLean.PEPS.Approximation.vectorTensorToGraphTensor_approximation
#print axioms TNLean.PEPS.Approximation.Pinned.RegionConfiguration
#print axioms TNLean.PEPS.Approximation.Pinned.joinConfigurations
#print axioms TNLean.PEPS.Approximation.Pinned.coefficientMatrix
#print axioms TNLean.PEPS.Approximation.Pinned.reducedDensity
#print axioms TNLean.PEPS.Approximation.Pinned.vonNeumannEntropy
#print axioms TNLean.PEPS.Approximation.Pinned.boundaryCard
#print axioms TNLean.PEPS.Approximation.joinConfigurations_eq_assembleRegion
#print axioms TNLean.PEPS.Approximation.regionReducedDensity_pinnedTensorToGraphTensor
#print axioms TNLean.PEPS.Approximation.regionReducedDensity_vectorTensorToGraphTensor
#print axioms TNLean.PEPS.Approximation.entropy_pinnedTensorToGraphTensor
#print axioms TNLean.PEPS.Approximation.forwardSquareBoundaryEquiv
#print axioms TNLean.PEPS.Approximation.boundaryCard_eq_graph

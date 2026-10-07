/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SquareGridBounds
import TNLean.PEPS.Approximation.RegionalStates

/-! # Standard-axiom guards for exact square-grid state transport -/

set_option linter.hashCommand false

/-- info: 'TNLean.PEPS.Approximation.stateVector_pinnedTensorToGraphTensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.Approximation.stateVector_pinnedTensorToGraphTensor

/-- info: 'TNLean.PEPS.Approximation.stateVector_vectorTensorToGraphTensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.Approximation.stateVector_vectorTensorToGraphTensor

/-- info: 'TNLean.PEPS.Approximation.isometry_squareGridState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.Approximation.isometry_squareGridState

/-- info: 'TNLean.PEPS.Approximation.Vector.PhaseErrorAtMost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.Approximation.Vector.PhaseErrorAtMost

/-- info: 'TNLean.PEPS.Approximation.phaseErrorAtMost_vectorTensorToGraphTensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.Approximation.phaseErrorAtMost_vectorTensorToGraphTensor

/-- info: 'TNLean.PEPS.Approximation.Vector.Tensor.maxBondDim_le_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.Approximation.Vector.Tensor.maxBondDim_le_iff

/-- info: 'TNLean.PEPS.Approximation.vectorTensorToGraphTensor_bondDim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.Approximation.vectorTensorToGraphTensor_bondDim

/-- info: 'TNLean.PEPS.Approximation.maxBondDim_vectorTensorToGraphTensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.Approximation.maxBondDim_vectorTensorToGraphTensor

/-- info: 'TNLean.PEPS.Approximation.pinnedTensorToGraphTensor_bond_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.Approximation.pinnedTensorToGraphTensor_bond_bounds

/-- info: 'TNLean.PEPS.Approximation.norm_stateVector_pinnedTensorToGraphTensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.Approximation.norm_stateVector_pinnedTensorToGraphTensor

/-- info: 'TNLean.PEPS.Approximation.pinnedTensorToGraphTensor_normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.Approximation.pinnedTensorToGraphTensor_normalized

/-- info: 'TNLean.PEPS.Approximation.pinnedTensorToGraphTensor_approximation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.Approximation.pinnedTensorToGraphTensor_approximation

/-- info: 'TNLean.PEPS.Approximation.vectorTensorToGraphTensor_approximation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.Approximation.vectorTensorToGraphTensor_approximation

/-- info: 'TNLean.PEPS.Approximation.Pinned.RegionConfiguration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.Approximation.Pinned.RegionConfiguration

/-- info: 'TNLean.PEPS.Approximation.Pinned.joinConfigurations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.Approximation.Pinned.joinConfigurations

/-- info: 'TNLean.PEPS.Approximation.Pinned.coefficientMatrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.Approximation.Pinned.coefficientMatrix

/-- info: 'TNLean.PEPS.Approximation.Pinned.reducedDensity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.Approximation.Pinned.reducedDensity

/-- info: 'TNLean.PEPS.Approximation.Pinned.vonNeumannEntropy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.Approximation.Pinned.vonNeumannEntropy

/-- info: 'TNLean.PEPS.Approximation.Pinned.boundaryCard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.Approximation.Pinned.boundaryCard

/-- info: 'TNLean.PEPS.Approximation.joinConfigurations_eq_assembleRegion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.Approximation.joinConfigurations_eq_assembleRegion

/-- info: 'TNLean.PEPS.Approximation.regionReducedDensity_pinnedTensorToGraphTensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.Approximation.regionReducedDensity_pinnedTensorToGraphTensor

/-- info: 'TNLean.PEPS.Approximation.regionReducedDensity_vectorTensorToGraphTensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.Approximation.regionReducedDensity_vectorTensorToGraphTensor

/-- info: 'TNLean.PEPS.Approximation.entropy_pinnedTensorToGraphTensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.Approximation.entropy_pinnedTensorToGraphTensor

/-- info: 'TNLean.PEPS.Approximation.forwardSquareBoundaryEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.Approximation.forwardSquareBoundaryEquiv

/-- info: 'TNLean.PEPS.Approximation.boundaryCard_eq_graph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.Approximation.boundaryCard_eq_graph

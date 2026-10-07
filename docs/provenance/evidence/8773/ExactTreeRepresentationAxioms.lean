/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ExactSquareRepresentation

/-!
# Raw axiom report for exact tree PEPS

This query file prints the dependencies of all 40 authored public declarations.
Permanent checked expectations live in the corresponding test module; this file
is retained separately to capture an unfiltered report.
-/

set_option linter.hashCommand false

#print axioms TNLean.PEPS.ExactTreeRepresentation.configurationEquiv
#print axioms TNLean.PEPS.ExactTreeRepresentation.bondDim
#print axioms TNLean.PEPS.ExactTreeRepresentation.decode
#print axioms TNLean.PEPS.ExactTreeRepresentation.encode
#print axioms TNLean.PEPS.ExactTreeRepresentation.decode_encode
#print axioms TNLean.PEPS.ExactTreeRepresentation.decode_injective
#print axioms TNLean.PEPS.ExactTreeRepresentation.bondDim_pos
#print axioms TNLean.PEPS.ExactTreeRepresentation.bondDim_le
#print axioms TNLean.PEPS.ExactTreeRepresentation.Ports
#print axioms TNLean.PEPS.ExactTreeRepresentation.Ports.ofConnected
#print axioms TNLean.PEPS.ExactTreeRepresentation.localLabel
#print axioms TNLean.PEPS.ExactTreeRepresentation.IsConsistent
#print axioms TNLean.PEPS.ExactTreeRepresentation.tensor
#print axioms TNLean.PEPS.ExactTreeRepresentation.localLabel_encode
#print axioms TNLean.PEPS.ExactTreeRepresentation.isConsistent_encode
#print axioms TNLean.PEPS.ExactTreeRepresentation.tensor_component_encode
#print axioms TNLean.PEPS.ExactTreeRepresentation.isConsistent_of_component_ne_zero
#print axioms TNLean.PEPS.ExactTreeRepresentation.localLabel_eq_of_adj
#print axioms TNLean.PEPS.ExactTreeRepresentation.localLabel_eq_of_consistent
#print axioms TNLean.PEPS.ExactTreeRepresentation.eq_encode_of_consistent
#print axioms TNLean.PEPS.ExactTreeRepresentation.tensor_product_eq_zero
#print axioms TNLean.PEPS.ExactTreeRepresentation.stateCoeff_tensor
#print axioms TNLean.PEPS.ExactTreeRepresentation.stateCoeff_tensor_eq
#print axioms TNLean.PEPS.ExactTreeRepresentation.stateCoeff_tensor_ne_zero
#print axioms TNLean.PEPS.ExactTreeRepresentation.exists_exact_tree_tensor
#print axioms TNLean.PEPS.ExactTreeRepresentation.singletonTensor
#print axioms TNLean.PEPS.ExactTreeRepresentation.stateCoeff_singletonTensor
#print axioms TNLean.PEPS.ExactTreeRepresentation.exists_exact_tensor
#print axioms TNLean.PEPS.ExactTreeRepresentation.stateCoeff_of_isEmpty
#print axioms TNLean.PEPS.ExactTreeRepresentation.exists_exact_square_tensor
#print axioms TNLean.PEPS.ExactTreeRepresentation.exists_exact_square_tree_tensor
#print axioms TNLean.PEPS.ExactTreeRepresentation.exists_exact_unit_square_tensor
#print axioms TNLean.PEPS.ExactTreeRepresentation.exists_exact_square_tensor_bounded
#print axioms TNLean.PEPS.ExactTreeRepresentation.exists_exact_square_tensor_polynomial
#print axioms TNLean.PEPS.squareLatticeGraph_eq_boxProd
#print axioms TNLean.PEPS.squareLatticeGraph_preconnected
#print axioms TNLean.PEPS.squareLatticeGraph_connected
#print axioms TNLean.PEPS.squareLatticeGraph_connected_iff
#print axioms TNLean.PEPS.squareLatticeVertex_nontrivial
#print axioms TNLean.PEPS.ExactTreeRepresentation.exists_exact_square_tensor_outer_power

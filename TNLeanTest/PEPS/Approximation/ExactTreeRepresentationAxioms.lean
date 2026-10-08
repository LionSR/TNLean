/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ExactSquareRepresentation

/-!
# Permanent axiom checks for exact tree PEPS

These checks cover all 40 authored public declarations in the generic
construction, square-lattice geometry, and finite-size specialization.
Expected reports come from the parent task's native axiom queries.
-/

set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.ExactTreeRepresentation.configurationEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.ExactTreeRepresentation.configurationEquiv

/--
info: 'TNLean.PEPS.ExactTreeRepresentation.bondDim' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.ExactTreeRepresentation.bondDim

/--
info: 'TNLean.PEPS.ExactTreeRepresentation.decode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.ExactTreeRepresentation.decode

/--
info: 'TNLean.PEPS.ExactTreeRepresentation.encode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.ExactTreeRepresentation.encode

/--
info: 'TNLean.PEPS.ExactTreeRepresentation.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.ExactTreeRepresentation.decode_encode

/--
info: 'TNLean.PEPS.ExactTreeRepresentation.decode_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.ExactTreeRepresentation.decode_injective

/--
info: 'TNLean.PEPS.ExactTreeRepresentation.bondDim_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.ExactTreeRepresentation.bondDim_pos

/--
info: 'TNLean.PEPS.ExactTreeRepresentation.bondDim_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.ExactTreeRepresentation.bondDim_le

/--
info: 'TNLean.PEPS.ExactTreeRepresentation.Ports' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.ExactTreeRepresentation.Ports

/--
info: 'TNLean.PEPS.ExactTreeRepresentation.Ports.ofConnected' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.ExactTreeRepresentation.Ports.ofConnected

/--
info: 'TNLean.PEPS.ExactTreeRepresentation.localLabel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.ExactTreeRepresentation.localLabel

/--
info: 'TNLean.PEPS.ExactTreeRepresentation.IsConsistent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.ExactTreeRepresentation.IsConsistent

/--
info: 'TNLean.PEPS.ExactTreeRepresentation.tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.ExactTreeRepresentation.tensor

/--
info: 'TNLean.PEPS.ExactTreeRepresentation.localLabel_encode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.ExactTreeRepresentation.localLabel_encode

/--
info: 'TNLean.PEPS.ExactTreeRepresentation.isConsistent_encode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.ExactTreeRepresentation.isConsistent_encode

/--
info: 'TNLean.PEPS.ExactTreeRepresentation.tensor_component_encode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.ExactTreeRepresentation.tensor_component_encode

/--
info: 'TNLean.PEPS.ExactTreeRepresentation.isConsistent_of_component_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.ExactTreeRepresentation.isConsistent_of_component_ne_zero

/--
info: 'TNLean.PEPS.ExactTreeRepresentation.localLabel_eq_of_adj' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.ExactTreeRepresentation.localLabel_eq_of_adj

/--
info: 'TNLean.PEPS.ExactTreeRepresentation.localLabel_eq_of_consistent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.ExactTreeRepresentation.localLabel_eq_of_consistent

/--
info: 'TNLean.PEPS.ExactTreeRepresentation.eq_encode_of_consistent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.ExactTreeRepresentation.eq_encode_of_consistent

/--
info: 'TNLean.PEPS.ExactTreeRepresentation.tensor_product_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.ExactTreeRepresentation.tensor_product_eq_zero

/--
info: 'TNLean.PEPS.ExactTreeRepresentation.stateCoeff_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.ExactTreeRepresentation.stateCoeff_tensor

/--
info: 'TNLean.PEPS.ExactTreeRepresentation.stateCoeff_tensor_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.ExactTreeRepresentation.stateCoeff_tensor_eq

/--
info: 'TNLean.PEPS.ExactTreeRepresentation.stateCoeff_tensor_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.ExactTreeRepresentation.stateCoeff_tensor_ne_zero

/--
info: 'TNLean.PEPS.ExactTreeRepresentation.exists_exact_tree_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.ExactTreeRepresentation.exists_exact_tree_tensor

/--
info: 'TNLean.PEPS.ExactTreeRepresentation.singletonTensor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.ExactTreeRepresentation.singletonTensor

/--
info: 'TNLean.PEPS.ExactTreeRepresentation.stateCoeff_singletonTensor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.ExactTreeRepresentation.stateCoeff_singletonTensor

/--
info: 'TNLean.PEPS.ExactTreeRepresentation.exists_exact_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.ExactTreeRepresentation.exists_exact_tensor

/--
info: 'TNLean.PEPS.ExactTreeRepresentation.stateCoeff_of_isEmpty' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.ExactTreeRepresentation.stateCoeff_of_isEmpty

/--
info: 'TNLean.PEPS.ExactTreeRepresentation.exists_exact_square_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.ExactTreeRepresentation.exists_exact_square_tensor

/--
info: 'TNLean.PEPS.ExactTreeRepresentation.exists_exact_square_tree_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.ExactTreeRepresentation.exists_exact_square_tree_tensor

/--
info: 'TNLean.PEPS.ExactTreeRepresentation.exists_exact_unit_square_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.ExactTreeRepresentation.exists_exact_unit_square_tensor

/--
info: 'TNLean.PEPS.ExactTreeRepresentation.exists_exact_square_tensor_bounded' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.ExactTreeRepresentation.exists_exact_square_tensor_bounded

/--
info: 'TNLean.PEPS.ExactTreeRepresentation.exists_exact_square_tensor_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.ExactTreeRepresentation.exists_exact_square_tensor_polynomial

/--
info: 'TNLean.PEPS.squareLatticeGraph_eq_boxProd' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.squareLatticeGraph_eq_boxProd

/--
info: 'TNLean.PEPS.squareLatticeGraph_preconnected' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.squareLatticeGraph_preconnected

/--
info: 'TNLean.PEPS.squareLatticeGraph_connected' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.squareLatticeGraph_connected

/--
info: 'TNLean.PEPS.squareLatticeGraph_connected_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.squareLatticeGraph_connected_iff

/--
info: 'TNLean.PEPS.squareLatticeVertex_nontrivial' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.squareLatticeVertex_nontrivial

/--
info: 'TNLean.PEPS.ExactTreeRepresentation.exists_exact_square_tensor_outer_power' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.ExactTreeRepresentation.exists_exact_square_tensor_outer_power

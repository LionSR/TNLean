/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.HoleEncoder

/-!
# Axiom guards for the exact one-hole encoder

These guards import the production encoder and require its public declarations
to use only the three standard logical axioms.
-/

set_option linter.hashCommand false

/-- info: 'TNLean.PEPS.coordinateResetMatrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.PEPS.coordinateResetMatrix

/-- info: 'TNLean.PEPS.coordinateResetMatrix_gram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.PEPS.coordinateResetMatrix_gram

/-- info: 'TNLean.PEPS.finrank_coordinateSubspaceES' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.PEPS.finrank_coordinateSubspaceES

/-- info: 'TNLean.PEPS.coordinateRangeProjector_eq_sum_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.PEPS.coordinateRangeProjector_eq_sum_basis

/-- info: 'TNLean.PEPS.identityHoleEncoder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.PEPS.identityHoleEncoder

/-- info: 'TNLean.PEPS.identityHoleEncoder_gram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.PEPS.identityHoleEncoder_gram

/-- info: 'TNLean.PEPS.identityHoleEncoder_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.PEPS.identityHoleEncoder_mulVec

/-- info: 'TNLean.PEPS.identityHoleEncoder_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.PEPS.identityHoleEncoder_norm

/-- info: 'TNLean.PEPS.HoleEncoderTag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.PEPS.HoleEncoderTag

/-- info: 'TNLean.PEPS.holeEncoderBasis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.PEPS.holeEncoderBasis

/-- info: 'TNLean.PEPS.card_holeEncoderTag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.PEPS.card_holeEncoderTag

/-- info: 'TNLean.PEPS.card_holeEncoderTag_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.PEPS.card_holeEncoderTag_le

/-- info: 'TNLean.PEPS.holeEncoder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.PEPS.holeEncoder

/-- info: 'TNLean.PEPS.holeEncoder_gram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.PEPS.holeEncoder_gram

/-- info: 'TNLean.PEPS.holeEncoder_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.PEPS.holeEncoder_apply

/-- info: 'TNLean.PEPS.holeEncoder_eq_zero_of_not_reset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.PEPS.holeEncoder_eq_zero_of_not_reset

/-- info: 'TNLean.PEPS.holeEncoder_eq_zero_of_complement_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.PEPS.holeEncoder_eq_zero_of_complement_ne

/-- info: 'TNLean.PEPS.holeEncoder_opNorm_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.PEPS.holeEncoder_opNorm_le_one

/-- info: 'TNLean.PEPS.holeEncoder_norm_eq_projector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.PEPS.holeEncoder_norm_eq_projector

/-- info: 'TNLean.PEPS.holeEncoder_norm_eq_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.PEPS.holeEncoder_norm_eq_of_mem

/-- info: 'TNLean.PEPS.holeEncoder_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.PEPS.holeEncoder_norm_le

/-- info: 'TNLean.PEPS.holeEncoder_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.PEPS.holeEncoder_empty

/-- info: 'TNLean.PEPS.holeEncoder_zero_spaces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.PEPS.holeEncoder_zero_spaces

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.HoleEncoder

/-!
# Raw axiom audit for the exact one-hole encoder

Print every public declaration separately for an unguarded dependency report.
-/

set_option linter.hashCommand false

#print axioms TNLean.PEPS.coordinateResetMatrix
#print axioms TNLean.PEPS.coordinateResetMatrix_gram
#print axioms TNLean.PEPS.finrank_coordinateSubspaceES
#print axioms TNLean.PEPS.coordinateRangeProjector_eq_sum_basis
#print axioms TNLean.PEPS.identityHoleEncoder
#print axioms TNLean.PEPS.identityHoleEncoder_gram
#print axioms TNLean.PEPS.identityHoleEncoder_mulVec
#print axioms TNLean.PEPS.identityHoleEncoder_norm
#print axioms TNLean.PEPS.HoleEncoderTag
#print axioms TNLean.PEPS.holeEncoderBasis
#print axioms TNLean.PEPS.card_holeEncoderTag
#print axioms TNLean.PEPS.card_holeEncoderTag_le
#print axioms TNLean.PEPS.holeEncoder
#print axioms TNLean.PEPS.holeEncoder_gram
#print axioms TNLean.PEPS.holeEncoder_apply
#print axioms TNLean.PEPS.holeEncoder_eq_zero_of_not_reset
#print axioms TNLean.PEPS.holeEncoder_eq_zero_of_complement_ne
#print axioms TNLean.PEPS.holeEncoder_opNorm_le_one
#print axioms TNLean.PEPS.holeEncoder_norm_eq_projector
#print axioms TNLean.PEPS.holeEncoder_norm_le
#print axioms TNLean.PEPS.holeEncoder_empty
#print axioms TNLean.PEPS.holeEncoder_zero_spaces

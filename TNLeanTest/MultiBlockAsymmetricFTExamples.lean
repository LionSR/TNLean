/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.MultiBlock.Multiplicity
import TNLean.MPS.Examples.MultiBlock.NoGauge
import TNLean.MPS.Examples.MultiBlock.OneBlock
import TNLean.MPS.Examples.MultiBlock.Periodic
import TNLean.MPS.Examples.MultiBlock.RunningFactorization
import TNLean.MPS.Examples.MultiBlock.SharpnessOneBlockGeneral
import TNLean.MPS.Examples.MultiBlock.WorkedAdaptedBasis

/-!
# Axiom checks for the examples of the asymmetric fundamental theorem

The examples of *The asymmetric fundamental theorem of matrix product states* formalized in
`TNLean.MPS.Examples.MultiBlock`: the periodic tensor, the running example, the example without a
sitewise gauge, the multiplicity example, the one-block examples and the worked example. Each check
pins the standard axioms of one declaration.
-/

/-! ### Axioms of the examples -/

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Periodic.wordSpan_tensorC_of_odd'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Periodic.wordSpan_tensorC_of_odd

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Periodic.wordSpan_tensorC_of_even'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Periodic.wordSpan_tensorC_of_even

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Periodic.finrank_wordSpan_tensorC'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Periodic.finrank_wordSpan_tensorC

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Periodic.not_isNormal_tensorC'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Periodic.not_isNormal_tensorC

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Periodic.isIrreducibleAction_tensorC'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Periodic.isIrreducibleAction_tensorC

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Running.exists_multiBlockCompression_gauge_one'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Running.exists_multiBlockCompression_gauge_one

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Running.exists_multiBlockCompression_gauge_unipotent'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Running.exists_multiBlockCompression_gauge_unipotent

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Running.unipotent_conj_tensorB'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Running.unipotent_conj_tensorB

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Running.left_mul_pow_ne_smul'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Running.left_mul_pow_ne_smul

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Running.remainder_pow_ne_zero'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Running.remainder_pow_ne_zero

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Running.isInvariantSubmodule_tensorB_iff'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Running.isInvariantSubmodule_tensorB_iff

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Running.ord_flagVec_cases_of_z_eq_zero'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Running.ord_flagVec_cases_of_z_eq_zero

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Running.exists_multiBlockCompression_each_order'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Running.exists_multiBlockCompression_each_order

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Running.exists_multiBlockCompression_upper'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Running.exists_multiBlockCompression_upper

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Running.exists_left_eq_upper_of_ord_lt'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Running.exists_left_eq_upper_of_ord_lt

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Running.exists_multiBlockCompression_swap'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Running.exists_multiBlockCompression_swap

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Running.exists_left_eq_swap_of_ord_gt'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Running.exists_left_eq_swap_of_ord_gt

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Running.matching_left_right_gOne_redSwap'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Running.matching_left_right_gOne_redSwap

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Running.isAdaptedFactorization_gOne_redSwap'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Running.isAdaptedFactorization_gOne_redSwap

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Running.exists_eval_zero_eq_zero_and_eval_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Running.exists_eval_zero_eq_zero_and_eval_eq

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Running.eq_one_and_eq_one_of_forall_add_mul_pow_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Running.eq_one_and_eq_one_of_forall_add_mul_pow_eq

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.NoGauge.trace_evalWord_tensorB_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.NoGauge.trace_evalWord_tensorB_eq

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.NoGauge.trace_evalWord_tensorB'_eq_one_of_eq_replicate'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.NoGauge.trace_evalWord_tensorB'_eq_one_of_eq_replicate

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.NoGauge.trace_evalWord_tensorB'_eq_zero_of_ne_replicate'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.NoGauge.trace_evalWord_tensorB'_eq_zero_of_ne_replicate

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.NoGauge.tensorB_one_mul_zero_and_tensorB'_commute'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.NoGauge.tensorB_one_mul_zero_and_tensorB'_commute

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.NoGauge.isInvariantSubmodule_span_tensorB_iff'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.NoGauge.isInvariantSubmodule_span_tensorB_iff

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.NoGauge.isInvariantSubmodule_span_tensorB'_iff'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.NoGauge.isInvariantSubmodule_span_tensorB'_iff

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.NoGauge.not_exists_conj_tensorB_eq_tensorB''
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.NoGauge.not_exists_conj_tensorB_eq_tensorB'

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.OneBlock.isInvariantSubmodule_span_tensorB_iff'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.OneBlock.isInvariantSubmodule_span_tensorB_iff

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.OneBlock.z_eq_one_and_gInt_conj'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.OneBlock.z_eq_one_and_gInt_conj

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.OneBlock.flagVec_one_firstCompression_and_lastCompression'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.OneBlock.flagVec_one_firstCompression_and_lastCompression

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.OneBlock.eq_toFlagData_firstCompression_or_lastCompression'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.OneBlock.eq_toFlagData_firstCompression_or_lastCompression

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.OneBlock.left_right_matching_firstCompression_lastCompression'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.OneBlock.left_right_matching_firstCompression_lastCompression

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.OneBlock.left_mulVec_e_one_and_left_mul_tensorB'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.OneBlock.left_mulVec_e_one_and_left_mul_tensorB

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.OneBlock.remainder_lastCompression_eq_zero_and_firstCompression_ne_zero'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  MultiBlockExamples.OneBlock.remainder_lastCompression_eq_zero_and_firstCompression_ne_zero

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.SharpnessOneBlock.exists_multiBlockCompression_block_first'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.SharpnessOneBlock.exists_multiBlockCompression_block_first

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.SharpnessOneBlock.exists_multiBlockCompression_block_last'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.SharpnessOneBlock.exists_multiBlockCompression_block_last

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.SharpnessOneBlock.rowE0_mul_pow_and_rowOnes_mul_pow'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.SharpnessOneBlock.rowE0_mul_pow_and_rowOnes_mul_pow

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.SharpnessOneBlock.exists_rowOnes_mul_pow_eq_smul_iff'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.SharpnessOneBlock.exists_rowOnes_mul_pow_eq_smul_iff

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.SharpnessOneBlock.exists_length_eq_sub_one_not_exists_smul'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.SharpnessOneBlock.exists_length_eq_sub_one_not_exists_smul

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.SharpnessOneBlock.pow_mul_right_eq_of_eq_colE0'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.SharpnessOneBlock.pow_mul_right_eq_of_eq_colE0

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.SharpnessOneBlock.tensorBGen_one'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.SharpnessOneBlock.tensorBGen_one

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.SharpnessOneBlock.tensorBGen_two'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.SharpnessOneBlock.tensorBGen_two

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Multiplicity.wordSpan_tensorC_three_eq_top_and_isNormal'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Multiplicity.wordSpan_tensorC_three_eq_top_and_isNormal

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Multiplicity.isInvariantSubmodule_lineTensor'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Multiplicity.isInvariantSubmodule_lineTensor

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Multiplicity.span_eq_of_lineTensor_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Multiplicity.span_eq_of_lineTensor_eq

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Multiplicity.commute_tensorB_iff_eq_kronMat'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Multiplicity.commute_tensorB_iff_eq_kronMat

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Multiplicity.exists_split_multiBlockCompression_kronRow'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Multiplicity.exists_split_multiBlockCompression_kronRow

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Multiplicity.exists_left_eq_kronRow_of_remainder_eq_zero'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Multiplicity.exists_left_eq_kronRow_of_remainder_eq_zero

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Multiplicity.exists_left_mul_evalWord_eq_smul_iff'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Multiplicity.exists_left_mul_evalWord_eq_smul_iff

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Multiplicity.matching_left_splitRed_of_span_ne'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Multiplicity.matching_left_splitRed_of_span_ne

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Multiplicity.matching_left_redOne_redAt'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Multiplicity.matching_left_redOne_redAt

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Worked.wordSpan_tensorC₁_three_eq_top_and_isNormal'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Worked.wordSpan_tensorC₁_three_eq_top_and_isNormal

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Worked.isInvariantSubmodule_span_tensorT_iff_and_mulVec_eq_zero'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Worked.isInvariantSubmodule_span_tensorT_iff_and_mulVec_eq_zero

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Worked.redG_spec'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Worked.redG_spec

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Worked.redGt_spec'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Worked.redGt_spec

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Worked.flagVec_redG_redGt_and_matching'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Worked.flagVec_redG_redGt_and_matching

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Worked.finrank_flagVec_redG_inf_flagVec_redGt'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Worked.finrank_flagVec_redG_inf_flagVec_redGt

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Worked.inf_sup_intertwiner_redG_redGt'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Worked.inf_sup_intertwiner_redG_redGt

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Worked.isAdaptedFactorization_redG_redGt'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Worked.isAdaptedFactorization_redG_redGt

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Worked.not_exists_left_redGt_eq_smul_left_redG'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Worked.not_exists_left_redGt_eq_smul_left_redG

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Worked.trace_evalWord_tensorB_eq_add'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Worked.trace_evalWord_tensorB_eq_add

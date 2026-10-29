/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.RoundedPeriodicApproximation
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Foundation checks for periodic coarsening and the quadratic logarithmic hierarchy. -/

open TNLean.MPS.AreaLaw.LocalSolution

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
      ``periodicCoarseEdge,
      ``card_periodicCoarseEdge_fibre,
      ``finRotate_val_eq_succ_or_zero,
      ``periodicPhysicalCoordinate,
      ``periodicPhysicalDistance,
      ``periodicPhysicalCoordinate_lt,
      ``periodicCoarseEdge_internal_centre,
      ``periodicCoarseEdge_support,
      ``periodicCoarseEdge_zero_support,
      ``periodicCoarseEdge_support_all,
      ``norm_edgePartition_le_of_fibre_card,
      ``periodicCoarseOperator,
      ``sum_periodicCoarseOperator,
      ``periodicCoarseOperator_mem_supportedOperators,
      ``isHermitian_periodicCoarseOperator,
      ``residual_periodicCoarseOperator_le,
      ``centeredNorm_periodicCoarseOperator_le,
      ``hierarchyTruncationError_mul_length_le_eighth_gap,
      ``card_le_two_mul_re_trace_of_periodicHierarchyProjection_of_error,
      ``periodicCoarseProjection,
      ``exists_unit_mem_periodicCoarseProjection,
      ``card_le_two_mul_re_trace_of_periodicCoarseProjection,
      ``hierarchyProjectionLength_periodicCoarse_le,
      ``card_roundedPeriodicEdge_fibre_le,
      ``roundedPeriodicOperator,
      ``sum_roundedPeriodicOperator,
      ``roundedPeriodicOperator_mem_supportedOperators,
      ``isHermitian_roundedPeriodicOperator,
      ``residual_roundedPeriodicOperator_le,
      ``centeredNorm_roundedPeriodicOperator_le,
      ``roundedPeriodicProjection,
      ``exists_unit_mem_roundedPeriodicProjection,
      ``card_le_two_mul_re_trace_of_roundedPeriodicProjection,
      ``hierarchyProjectionLength_roundedPeriodic_le,
      ``roundedPeriodicProjectionRadius,
      ``roundedPeriodicProjectionRadius_pos,
      ``hierarchyProjectionLength_le_chosen_roundedPeriodicRadius,
      ``roundedPeriodicProjectionRadius_lt,
      ``exists_unit_mem_roundedPeriodicProjection_of_chosen_radius,
      ``card_le_two_mul_re_trace_of_roundedPeriodicProjection_of_chosen_radius] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

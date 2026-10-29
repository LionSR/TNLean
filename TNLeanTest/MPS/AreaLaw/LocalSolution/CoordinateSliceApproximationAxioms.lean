/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.CoordinateSliceBox
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Foundation checks for the coordinate-slice construction from physical local terms. -/

open TNLean.MPS.AreaLaw.LocalSolution

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``edgePartition, ``sum_edgePartition, ``norm_edgePartition_le,
      ``isHermitian_edgePartition, ``centered_edgePartition, ``residual_edgePartition_le,
      ``centeredNorm_edgePartition_le, ``centeredNorm_edgePartition_le_two_mul,
      ``edgePartition_mem_supportedOperators,
      ``coordinateSlice, ``coordinateSliceLower, ``coordinateSlice_eq_lower_or_succ,
      ``coordinateSliceEdge, ``coordinateSliceEdge_support, ``coordinateSlice_lt,
      ``coordinateSliceEdge_closing_support, ``natDist_coordinate_le_of_dist_le,
      ``coordinateSliceOperator, ``sum_coordinateSliceOperator,
      ``coordinateSliceOperator_mem_supportedOperators,
      ``coordinateSliceOperator_mem_supportedOperators_of_metric,
      ``isHermitian_coordinateSliceOperator, ``residual_coordinateSliceOperator_le,
      ``centeredNorm_coordinateSliceOperator_le,
      ``centeredNorm_coordinateSliceOperator_le_two_mul,
      ``coordinateSliceOperator_closing_mem_supportedOperators,
      ``coordinateSliceProjection, ``exists_unit_mem_coordinateSliceProjection,
      ``card_le_two_mul_re_trace_of_coordinateSliceProjection,
      ``hierarchyProjectionLength_coordinateSlices_le,
      ``coordinateSide_le_card_box, ``coordinateBox_slice_extent,
      ``coordinateBox_ball_subset_strip, ``hierarchyProjectionLength_coordinateBox_le,
      ``exists_unit_mem_coordinateSliceProjection_of_box,
      ``card_le_two_mul_re_trace_of_coordinateSliceProjection_of_box] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

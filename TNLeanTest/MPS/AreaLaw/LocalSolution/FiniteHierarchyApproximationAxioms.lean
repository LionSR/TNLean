/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.FiniteHierarchyApproximation
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Foundation checks for the hierarchy constructed from finite physical edge data. -/

open TNLean.MPS.AreaLaw.LocalSolution

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``extendFiniteEdges, ``extendFiniteEdges_apply_fin,
      ``extendFiniteEdges_eq_zero, ``sum_extendFiniteEdges, ``sum_extendFiniteEdges_of_le,
      ``finiteHierarchyDepth, ``two_le_finiteHierarchyDepth,
      ``le_two_pow_finiteHierarchyDepth, ``finiteHierarchyDepth_le_clog_add_two,
      ``hierarchySum_hierarchyEdge_extend_add_zero, ``isHermitian_extendFiniteEdges,
      ``residual_extendFiniteEdges_le, ``centeredNorm_extendFiniteEdges_le,
      ``extendFiniteEdges_mem_supportedOperators,
      ``hierarchyEdge_extendFiniteEdges_mem_supportedOperators,
      ``hierarchyProjectionLength_finiteHierarchyDepth_le,
      ``hierarchyProjectionLength_finiteHierarchyDepth_mul_le,
      ``exists_unit_mem_periodicHierarchyProjection_of_finite,
      ``card_le_two_mul_re_trace_of_periodicHierarchyProjection_of_finite] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

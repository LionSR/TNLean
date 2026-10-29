/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.HierarchyApproximation
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Foundation checks for the constructed hierarchy, the edge sum, and the
quantitative final-state count under the physical Hamiltonian's spectral gap. -/

open TNLean.MPS.AreaLaw.LocalSolution

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``hierarchyProjection, ``hierarchyClosingProjection,
      ``norm_sub_hierarchyProjection_le, ``exists_unit_mem_hierarchyProjection,
      ``norm_sub_hierarchyClosingProjection_le, ``exists_unit_mem_hierarchyClosingProjection,
      ``hierarchySum_hierarchyEdge, ``hierarchySum_hierarchyEdge_add_zero,
      ``hierarchyEdge_mem_supportedOperators, ``abs_re_inner_sub_le_norm_sub,
      ``abs_re_inner_sub_le_of_norm_sub_le, ``card_le_two_mul_re_trace_of_approximation,
      ``periodicHierarchyProjection, ``exists_unit_mem_periodicHierarchyProjection,
      ``card_le_two_mul_re_trace_of_periodicHierarchyProjection] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

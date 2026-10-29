/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.MetricInteractionGraph
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Foundation checks for the interaction graph of a finite metric Hamiltonian. -/

open TNLean.Lattice

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``metricRangeGraph, ``metricRangeGraph_edist_le_one,
      ``metricRangeGraph_edist_le_two, ``dist_le_range_mul_walkLength,
      ``dist_le_range_mul_graphDist, ``metricRangeGraph_edist_lower_ceil,
      ``metricRangeGraph_zero_edist_eq_top, ``metricRangeBall, ``mem_metricRangeBall,
      ``coe_metricRangeBall, ``self_mem_metricRangeBall, ``metricRangeGraph_neighbor_card_le,
      ``metricRangeBall_graph_diameter_le_two, ``sum_norm_metricRangeBall_le,
      ``metricRangeBall_norm_budget_le, ``metricRangeBall_retained_support,
      ``metricRangeBall_initial_support, ``metricRangeGraph_omitted_threshold] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

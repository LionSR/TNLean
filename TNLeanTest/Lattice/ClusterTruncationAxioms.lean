/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ClusterExpansion.Truncation
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the inclusion–exclusion identity of Hastings'
truncated high-temperature expansion. -/

open TNLean.Lattice.ClusterExpansion

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``sum_pow_eq_sum_words, ``sum_words_contain_avoid,
    ``eq_of_isCluster_of_inter_nonempty, ``pairwiseDisjoint_of_admissible,
    ``biUnion_boundary_eq_of_admissible, ``card_add_card_biUnion_boundary_le,
    ``ite_noLargeCluster_eq_sum, ``mem_boundary_overlapGraph, ``hasSum_words_clusterPart,
    ``hasSum_truncatedExpTerm, ``exp_sub_truncatedExp,
    ``norm_trace_mul_exp_sub_truncatedExp_le] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

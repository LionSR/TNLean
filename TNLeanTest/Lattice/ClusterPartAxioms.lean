/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ClusterExpansion.ClusterPart
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the cluster part of Hastings' high-temperature
expansion and its single-cluster bound. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``TNLean.Lattice.ClusterExpansion.clusterPart,
    ``TNLean.Lattice.ClusterExpansion.clusterPart_eq_sum_powerset,
    ``TNLean.Lattice.ClusterExpansion.norm_trace_mul_clusterPart_le,
    ``TNLean.Lattice.ClusterExpansion.re_trace_exp_sub_sum_sub_sum_le,
    ``TNLean.Lattice.ClusterExpansion.norm_mul_exp_mul_sub_one_pow_nonneg,
    ``TNLean.Lattice.ClusterExpansion.exp_card_add_card_mul_le,
    ``TNLean.Lattice.ClusterExpansion.norm_trace_mul_clusterPart_le_pow,
    ``TNLean.Lattice.ClusterExpansion.norm_trace_mul_clusterPart_biUnion_le,
    ``TNLean.Lattice.ClusterExpansion.norm_trace_mul_exp_mul_clusterPart_mul_exp_le_pow,
    ``TNLean.Lattice.ClusterExpansion.clusterBoundary,
    ``TNLean.Lattice.ClusterExpansion.card_add_card_clusterBoundary_le] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

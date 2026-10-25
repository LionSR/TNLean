/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ClusterExpansion.PercolationSource
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for Hastings' percolation bound for clusters of large
diameter. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``TNLean.Lattice.ClusterExpansion.dist_le_of_mem_biUnion_of_connected,
    ``TNLean.Lattice.ClusterExpansion.card_ge_of_isLargeDiam,
    ``TNLean.Lattice.ClusterExpansion.card_add_card_boundary_le,
    ``TNLean.Lattice.ClusterExpansion.norm_trace_mul_exp_sub_truncatedExp_le_isLargeDiam,
    ``TNLean.Lattice.ClusterExpansion.norm_trace_mul_exp_sub_truncatedExp_le_isLargeDiam_dist] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

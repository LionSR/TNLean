/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ClusterExpansion.ClusterFactorization
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for Hastings' truncated operator as a sum of products
over clusters. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``TNLean.Lattice.ClusterExpansion.hasSum_words_clusterOp,
    ``TNLean.Lattice.ClusterExpansion.truncatedExp_eq_sum_clusterOp,
    ``TNLean.Lattice.ClusterExpansion.clusterOp_union,
    ``TNLean.Lattice.ClusterExpansion.biUnion_clusters,
    ``TNLean.Lattice.ClusterExpansion.clusterOp_eq_noncommProd_clusters,
    ``TNLean.Lattice.ClusterExpansion.truncatedExp_eq_sum_noncommProd_clusters,
    ``TNLean.Lattice.ClusterExpansion.clusterOp_mem_supportedOperators] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

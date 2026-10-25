/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ClusterExpansion.TruncatedProductForm
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for Hastings' truncated operator in matrix product
form. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``TNLean.Lattice.ClusterExpansion.noncommProd_apply_of_pairwiseDisjoint,
    ``TNLean.Lattice.ClusterExpansion.noLargeCluster_iff_filter,
    ``TNLean.Lattice.ClusterExpansion.truncatedExp_eq_mul,
    ``TNLean.Lattice.ClusterExpansion.sum_clusterOp_apply,
    ``TNLean.Lattice.ClusterExpansion.isLocalCoefficient_clusterCoeff,
    ``TNLean.Lattice.ClusterExpansion.sum_prod_clusterCoeff,
    ``TNLean.Lattice.ClusterExpansion.hasProductForm_sum_clusterOp,
    ``TNLean.Lattice.ClusterExpansion.hasProductForm_truncatedExp] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

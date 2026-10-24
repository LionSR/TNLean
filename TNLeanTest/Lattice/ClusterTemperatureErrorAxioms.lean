/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ClusterExpansion.TemperatureError
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the error bound of Hastings' truncated expansion at
every temperature. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``TNLean.Lattice.ClusterExpansion.sum_prod_le_exp_of_subset_powerset,
    ``TNLean.Lattice.ClusterExpansion.norm_trace_mul_exp_sub_truncatedExp_pow_le,
    ``TNLean.Lattice.ClusterExpansion.norm_trace_mul_exp_sub_truncatedExp_pow_le_percolation] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

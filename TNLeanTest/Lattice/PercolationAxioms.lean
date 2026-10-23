/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ClusterExpansion.Percolation
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the percolation sum of Hastings' cluster expansion. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.Lattice.sum_powersetCard_prod_le,
    ``TNLean.Lattice.sum_nonempty_powerset_prod_le_exp,
    ``TNLean.Lattice.sum_pow_le_of_forall_lt, ``TNLean.Lattice.sum_pow_le_of_card_le,
    ``TNLean.Lattice.pow_succ_div_one_sub_le, ``TNLean.Lattice.pow_eq_exp_neg_div,
    ``TNLean.Lattice.sum_nonempty_powerset_prod_le_percolation,
    ``TNLean.Lattice.sum_nonempty_powerset_prod_le_percolation_connected,
    ``TNLean.Lattice.exists_percolation_temperature] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

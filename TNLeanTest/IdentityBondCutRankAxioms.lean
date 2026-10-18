/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.IdentityBondCutRank
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Presence and permitted-axiom checks for heterogeneous identity-bond cut ranks

The two coefficient factorizations and their two rank consequences are audited without
assuming any normalization, injectivity or nonempty virtual alphabet.
-/

open TNLean.PEPS.DependentBondNetwork
open TNLean.PEPS.Approximation.DistributedOperatorContraction

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``flattening_network_one_eq_mul,
      ``rank_flattening_network_one_le,
      ``flattening_contractedOperator_column_eq_mul,
      ``rank_flattening_contractedOperator_column_le] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

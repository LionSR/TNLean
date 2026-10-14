/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicLifetimeIncidence
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom guard for the lifetime incidence counts of the dyadic hierarchy

The near-square and near-junction counts and the lifetime participation bound
must exist in the production module and depend only on standard logical axioms.
-/

set_option linter.hashCommand false

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in #[``TNLean.PEPS.Approximation.card_range_blockNear_le,
      ``TNLean.PEPS.Approximation.card_range_cornerNear_le,
      ``TNLean.PEPS.Approximation.card_dyadicSquare_near_le,
      ``TNLean.PEPS.Approximation.card_dyadicJunction_near_le,
      ``TNLean.PEPS.Approximation.card_gates_le_of_near] do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

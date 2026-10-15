/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicActiveLabelParties
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom guard for the active-label invariant in party form

The party form of the active-label invariant, the used parties of repaintings and junction
resizes, their nearness, and the lifetime participation bound must exist in the production
module and depend only on standard logical axioms.
-/

set_option linter.hashCommand false

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in #[``TNLean.PEPS.Approximation.levelLabels_eq_party,
      ``TNLean.PEPS.Approximation.levelLabels_empty_eq_party,
      ``TNLean.PEPS.Approximation.levelLabels_eq_party_of_subset,
      ``TNLean.PEPS.Approximation.repaintingUses_of_levelLabels,
      ``TNLean.PEPS.Approximation.incidentLabels_blockGuide_corner,
      ``TNLean.PEPS.Approximation.junctionUses_of_incidentLabels,
      ``TNLean.PEPS.Approximation.RepaintingUses.near,
      ``TNLean.PEPS.Approximation.JunctionUses.near,
      ``TNLean.PEPS.Approximation.card_dyadicJunction_uses_le,
      ``TNLean.PEPS.Approximation.card_gates_le_of_uses] do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

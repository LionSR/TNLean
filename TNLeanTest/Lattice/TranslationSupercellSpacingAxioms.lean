/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.TranslationSupercellSpacing
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the supercell translations of a ring that carry a
site far away. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
      ``TNLean.Lattice.pow_mem_supercell,
      ``SimpleGraph.ringNorm_sub_le_edist_cycleGraph,
      ``SimpleGraph.exists_lt_edist_add_cycleGraph,
      ``TNLean.Lattice.exists_mem_supercell_lt_edist_add] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProtocolCutCoordinates
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Presence and permitted-axiom checks for original-site cut coordinates

The named declarations are required to be present, and their collected axioms
are required to belong to the standard set consisting of propositional extensionality,
classical choice and quotient soundness. Each declaration and its axioms are reported.
-/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := #[
    ``TNLean.MPS.AreaLaw.ChainSweep.rank_partyPrefix_eq_cutMatrix,
    ``TNLean.MPS.AreaLaw.ChainSweep.rank_partyPrefix_last_eq_cutMatrix,
    ``TNLean.MPS.AreaLaw.ChainSweep.rank_cutMatrix_le_of_partyPrefix_bounds]
  for decl in names do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

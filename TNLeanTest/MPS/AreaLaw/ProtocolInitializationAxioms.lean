/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProtocolInitialization
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Axiom checks for the specified initial copies and their private preparation. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.MPS.AreaLaw.ChainSweep.length_initialFrames,
      ``TNLean.MPS.AreaLaw.ChainSweep.mem_initialFrames,
      ``TNLean.MPS.AreaLaw.ChainSweep.norm_initialFrames,
      ``TNLean.MPS.AreaLaw.ChainSweep.exists_initialization] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

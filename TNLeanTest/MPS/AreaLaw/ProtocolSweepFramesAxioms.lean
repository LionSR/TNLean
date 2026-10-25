/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProtocolSweepFrames
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Axiom checks for the initial and terminal owners, the actual birth targets
and environments, the band flanks, and the stage ownership recurrence. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.MPS.AreaLaw.ChainSweep.stageOwner,
      ``TNLean.MPS.AreaLaw.ChainSweep.stageFrame,
      ``TNLean.MPS.AreaLaw.ChainSweep.remainderBirthTarget,
      ``TNLean.MPS.AreaLaw.ChainSweep.blockBirthTarget,
      ``TNLean.MPS.AreaLaw.ChainSweep.leftBandTarget,
      ``TNLean.MPS.AreaLaw.ChainSweep.rightBandTarget,
      ``TNLean.MPS.AreaLaw.ChainSweep.afterRemainderBirth,
      ``TNLean.MPS.AreaLaw.ChainSweep.afterBlockBirth,
      ``TNLean.MPS.AreaLaw.ChainSweep.afterLeftTransfer,
      ``TNLean.MPS.AreaLaw.ChainSweep.afterRightTransfer,
      ``TNLean.MPS.AreaLaw.ChainSweep.stageOwner_zero,
      ``TNLean.MPS.AreaLaw.ChainSweep.stageOwner_last,
      ``TNLean.MPS.AreaLaw.ChainSweep.birth_targets_owned,
      ``TNLean.MPS.AreaLaw.ChainSweep.birth_environments,
      ``TNLean.MPS.AreaLaw.ChainSweep.left_band_owners,
      ``TNLean.MPS.AreaLaw.ChainSweep.first_left_death_environment,
      ``TNLean.MPS.AreaLaw.ChainSweep.right_band_owners,
      ``TNLean.MPS.AreaLaw.ChainSweep.afterRightTransfer_eq_stageFrame,
      ``TNLean.MPS.AreaLaw.ChainSweep.leftBandMain,
      ``TNLean.MPS.AreaLaw.ChainSweep.rightBandMain,
      ``TNLean.MPS.AreaLaw.ChainSweep.leftBandMain_eq_afterLeftTransfer,
      ``TNLean.MPS.AreaLaw.ChainSweep.rightBandMain_eq_afterRightTransfer,
      ``TNLean.MPS.AreaLaw.ChainSweep.rightBandMain_eq_stageFrame] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

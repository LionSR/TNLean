/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProtocolSweepHistory
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and axiom checks for the actual labelled stage-frame history. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.MPS.AreaLaw.ChainSweep.auxiliaryStage,
      ``TNLean.MPS.AreaLaw.ChainSweep.retiredAuxiliaryFrame,
      ``TNLean.MPS.AreaLaw.ChainSweep.auxiliaryFrameBefore,
      ``TNLean.MPS.AreaLaw.ChainSweep.sweepFrames,
      ``TNLean.MPS.AreaLaw.ChainSweep.leftAuxiliaryFrame,
      ``TNLean.MPS.AreaLaw.ChainSweep.afterLeftFrames,
      ``TNLean.MPS.AreaLaw.ChainSweep.afterRightFrames,
      ``TNLean.MPS.AreaLaw.ChainSweep.leftCopyLabel,
      ``TNLean.MPS.AreaLaw.ChainSweep.auxiliaryStage_lt_stageCount,
      ``TNLean.MPS.AreaLaw.ChainSweep.auxiliaryFrameBefore_zero,
      ``TNLean.MPS.AreaLaw.ChainSweep.auxiliaryFrameBefore_last,
      ``TNLean.MPS.AreaLaw.ChainSweep.sweepFrames_zero,
      ``TNLean.MPS.AreaLaw.ChainSweep.sweepFrames_last,
      ``TNLean.MPS.AreaLaw.ChainSweep.leftAuxiliaryFrame_right_unused,
      ``TNLean.MPS.AreaLaw.ChainSweep.auxiliaryFrameBefore_left_unused,
      ``TNLean.MPS.AreaLaw.ChainSweep.leftAuxiliaryFrame_zero,
      ``TNLean.MPS.AreaLaw.ChainSweep.leftAuxiliaryFrame_eq_update,
      ``TNLean.MPS.AreaLaw.ChainSweep.leftAuxiliaryFrame_spectator,
      ``TNLean.MPS.AreaLaw.ChainSweep.rightAuxiliaryUpdate_eq_next,
      ``TNLean.MPS.AreaLaw.ChainSweep.rightAuxiliaryUpdate_spectator,
      ``TNLean.MPS.AreaLaw.ChainSweep.afterRightFrames_eq_sweepFrames,
      ``TNLean.MPS.AreaLaw.ChainSweep.sweepFrames_select_auxiliary] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

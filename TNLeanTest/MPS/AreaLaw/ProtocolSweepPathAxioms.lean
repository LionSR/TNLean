/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProtocolSweepPath
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and axiom checks for the actual chain operation frame path. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.MPS.AreaLaw.ChainSweep.leftBandFrames,
      ``TNLean.MPS.AreaLaw.ChainSweep.rightBandFrames,
      ``TNLean.MPS.AreaLaw.ChainSweep.stageBoundaryFrames,
      ``TNLean.MPS.AreaLaw.ChainSweep.sweepOperationCount,
      ``TNLean.MPS.AreaLaw.ChainSweep.operationFrames,
      ``TNLean.MPS.AreaLaw.ChainSweep.stageBoundaryFrames_zero,
      ``TNLean.MPS.AreaLaw.ChainSweep.stageBoundaryFrames_one,
      ``TNLean.MPS.AreaLaw.ChainSweep.stageBoundaryFrames_two,
      ``TNLean.MPS.AreaLaw.ChainSweep.stageBoundaryFrames_left,
      ``TNLean.MPS.AreaLaw.ChainSweep.stageBoundaryFrames_first_left,
      ``TNLean.MPS.AreaLaw.ChainSweep.stageBoundaryFrames_ten,
      ``TNLean.MPS.AreaLaw.ChainSweep.stageBoundaryFrames_first_death,
      ``TNLean.MPS.AreaLaw.ChainSweep.stageBoundaryFrames_right,
      ``TNLean.MPS.AreaLaw.ChainSweep.stageBoundaryFrames_last,
      ``TNLean.MPS.AreaLaw.ChainSweep.stageBoundaryFrames_eighteen,
      ``TNLean.MPS.AreaLaw.ChainSweep.stageBoundaryFrames_left_entrance_perm,
      ``TNLean.MPS.AreaLaw.ChainSweep.leftBandFrames_eight_perm,
      ``TNLean.MPS.AreaLaw.ChainSweep.stageBoundaryFrames_right_entrance_perm,
      ``TNLean.MPS.AreaLaw.ChainSweep.rightBandFrames_eight_perm,
      ``TNLean.MPS.AreaLaw.ChainSweep.operationFrames_of_le,
      ``TNLean.MPS.AreaLaw.ChainSweep.operationFrames_stage,
      ``TNLean.MPS.AreaLaw.ChainSweep.operationFrames_zero,
      ``TNLean.MPS.AreaLaw.ChainSweep.operationFrames_last,
      ``TNLean.MPS.AreaLaw.ChainSweep.operationFrames_stageBoundary,
      ``TNLean.MPS.AreaLaw.ChainSweep.operationFrames_step] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProtocolSweepMiddle
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! UNEXECUTED importing fixture for a private source proposal. The candidate
and its selected source-only dependencies require elaboration. This file
provides no present declaration or axiom acceptance. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := #[
    ``TNLean.MPS.AreaLaw.ChainSweep.sweepMiddleStep,
    ``TNLean.MPS.AreaLaw.ChainSweep.sweepMiddleCircuit,
    ``TNLean.MPS.AreaLaw.ChainSweep.sweepMiddleStep_tail_identity,
    ``TNLean.MPS.AreaLaw.ChainSweep.sweepMiddleStep_first_padding,
    ``TNLean.MPS.AreaLaw.ChainSweep.sweepMiddleCircuit_participation_le_forty,
    ``TNLean.MPS.AreaLaw.ChainSweep.sweepMiddleCircuit_nonprivateCount_le,
    ``TNLean.MPS.AreaLaw.ChainSweep.sweepMiddleCircuit_resource_bounds,
    ``TNLean.MPS.AreaLaw.ChainSweep.sweepMiddleCircuit_norm_and_error]
  for decl in names do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

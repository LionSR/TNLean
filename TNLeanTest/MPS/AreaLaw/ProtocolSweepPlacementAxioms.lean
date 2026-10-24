/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProtocolSweepPlacement
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! UNEXECUTED importing fixture for the private placement proposal. Neither
the candidate nor its selected source-only dependencies have been elaborated
by this task. This guard establishes no present declaration or axiom result. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := #[
    ``TNLean.MPS.AreaLaw.ChainSweep.partyLevel,
    ``TNLean.MPS.AreaLaw.ChainSweep.stageParticipants_level_dist_le_two,
    ``TNLean.MPS.AreaLaw.ChainSweep.card_le_eight_of_subset_stageParticipants,
    ``TNLean.MPS.AreaLaw.ChainSweep.prefixCrossingLinks,
    ``TNLean.MPS.AreaLaw.ChainSweep.prefixCrossingLinks_zero,
    ``TNLean.MPS.AreaLaw.ChainSweep.prefixCrossingLinks_eq_empty_of_stageCount_lt,
    ``TNLean.MPS.AreaLaw.ChainSweep.prefixCrossingLinks_card_le_of_originalCircuit,
    ``TNLean.MPS.AreaLaw.ChainSweep.sweepMiddleCircuit_participants_subset_stage,
    ``TNLean.MPS.AreaLaw.ChainSweep.sweepMiddleCircuit_participants_level_dist_le_two,
    ``TNLean.MPS.AreaLaw.ChainSweep.sweepMiddleCircuit_participants_card_le_forty,
    ``TNLean.MPS.AreaLaw.ChainSweep.compressedMiddle_prefixCrossingLinks_card_le,
    ``TNLean.MPS.AreaLaw.ChainSweep.compressedMiddle_prefixCrossingLinks_card_le_24960]
  for decl in names do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

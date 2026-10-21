/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ChainStageIncidence
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Private unexecuted axiom fixture. It certifies nothing until the candidate
and its provider have been elaborated and this importing check has passed. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.MPS.AreaLaw.ChainSweep.remainder_participating_stage,
      ``TNLean.MPS.AreaLaw.ChainSweep.completed_participating_stage,
      ``TNLean.MPS.AreaLaw.ChainSweep.participatingStageIndices_card_le_two,
      ``TNLean.MPS.AreaLaw.ChainSweep.scheduledParticipationCount_eq_sum,
      ``TNLean.MPS.AreaLaw.ChainSweep.scheduledParticipationCount_le_thirtySix,
      ``TNLean.MPS.AreaLaw.ChainSweep.scheduledParticipationCount_le_forty] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

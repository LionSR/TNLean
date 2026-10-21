/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProtocolSweepGeometry
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Axiom checks for the chain block lengths, actual main-register fibres,
physical output dimensions, and scalar party and gate bounds. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.MPS.AreaLaw.ChainSweep.terminal_length_eq,
      ``TNLean.MPS.AreaLaw.ChainSweep.terminal_length_bounds,
      ``TNLean.MPS.AreaLaw.ChainSweep.stage_right_margin,
      ``TNLean.MPS.AreaLaw.ChainSweep.stage_left_margin,
      ``TNLean.MPS.AreaLaw.ChainSweep.card_mainSites_inr_le,
      ``TNLean.MPS.AreaLaw.ChainSweep.card_mainSites_inl_lt,
      ``TNLean.MPS.AreaLaw.ChainSweep.twenty_mul_stageCount_le,
      ``TNLean.MPS.AreaLaw.ChainSweep.card_party_le,
      ``TNLean.MPS.AreaLaw.ChainSweep.physicalDimension_le] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

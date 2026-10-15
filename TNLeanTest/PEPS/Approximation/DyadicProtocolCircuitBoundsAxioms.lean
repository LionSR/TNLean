/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicProtocolCircuitBounds
import Lean.Util.CollectAxioms

/-! Checks of logical dependencies for bounds of the actual supplied circuit. -/

open TNLean.PEPS.PairEffect.OriginalCircuit
open TNLean.PEPS.Approximation.DyadicProtocol
open TNLean.PEPS.Approximation.DyadicProtocol.IsDistributionProtocol

run_cmd do
  let env ← Lean.getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``participationCount_castLayouts, ``forall_participants_castLayouts,
      ``participationCount_originalCircuit_le, ``nonprivateCount_originalCircuit_le,
      ``exists_stage_participants_originalCircuit,
      ``isExpansionBounded_originalCircuit, ``isMonomialBounded_originalCircuit] do
    unless env.contains decl do
      throwError "Missing imported declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

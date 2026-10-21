/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProtocolTerminalCoordinates
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Axiom checks for the constructed terminal coordinates, their owner-local
factorization, and the physical marginal after tracing the auxiliary registers. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.MPS.AreaLaw.ChainSweep.terminalConfigurationEquiv,
      ``TNLean.MPS.AreaLaw.ChainSweep.terminalRegrouping,
      ``TNLean.MPS.AreaLaw.ChainSweep.localConfigurationEquiv_restrict,
      ``TNLean.MPS.AreaLaw.ChainSweep.physicalDensity_terminalRegrouping] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

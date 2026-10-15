/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceNetworkCoordinateBases
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom checks for finite source and discarded-memory coordinates -/

set_option linter.hashCommand false

run_cmd do
  let decls := #[
    ``TNLean.PEPS.PairEffect.SourceInventory.finiteDimensional_registers_slotLayout,
    ``TNLean.PEPS.PairEffect.SourceCircuit.finiteDimensional_allResidualSource_registers,
    ``TNLean.PEPS.PairEffect.SourceCircuit.allResidualSourceBasis,
    ``TNLean.PEPS.PairEffect.SourceCircuit.allPartyDiscardBasis]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in decls do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

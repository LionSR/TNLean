/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.SourceNetworkCoordinateBases
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom checks for finite source and discarded-memory coordinates -/

set_option linter.hashCommand false

run_cmd do
  let decls := #[
    ``TNLean.Lattice.PartyCircuit.SourceInventory.finiteDimensional_registers_slotLayout,
    ``TNLean.Lattice.PartyCircuit.SourceCircuit.finiteDimensional_allResidualSource_registers,
    ``TNLean.Lattice.PartyCircuit.SourceCircuit.allResidualSourceBasis,
    ``TNLean.Lattice.PartyCircuit.SourceCircuit.allPartyDiscardBasis]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in decls do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.SelectedPhysicalPrivateBasis
import TNLean.Lattice.Compression.SelectedPhysicalConfigurations
import TNLean.Lattice.Compression.SelectedPhysicalPartyGrouping
import TNLean.Lattice.Compression.SelectedPhysicalPrivateGrouping
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom checks for the actual physical/private columns and configurations -/

set_option linter.hashCommand false

run_cmd do
  let decls := #[
    ``TNLean.Lattice.PartyCircuit.selectedPhysicalPrivateBasis,
    ``TNLean.Lattice.PartyCircuit.selectedPhysicalPrivateBasis_apply_heq,
    ``TNLean.Lattice.PartyCircuit.selectedFamilyPhysicalConfigEquiv,
    ``TNLean.Lattice.PartyCircuit.partyProductMatrix_selectedFamilyPhysicalConfig,
    ``TNLean.Lattice.PartyCircuit.selectedPartyOrder,
    ``TNLean.Lattice.PartyCircuit.selectedPartyOrder_nodup,
    ``TNLean.Lattice.PartyCircuit.mem_selectedPartyOrder,
    ``TNLean.Lattice.PartyCircuit.selectedFamilyPhysicalPartyBasis_grouped,
    ``TNLean.Lattice.PartyCircuit.selectedPhysicalPrivateBasis_grouped]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in decls do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

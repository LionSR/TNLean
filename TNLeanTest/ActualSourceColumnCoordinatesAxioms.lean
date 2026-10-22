/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.ActualSourceColumnCoordinates
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom guard for actual source-column coordinates

The fixed source bases, literal column matrix and two coordinate identities
must exist in the production modules and depend only on standard logical axioms.
-/

set_option linter.hashCommand false

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in #[``TNLean.Lattice.PartyCircuit.SourceCircuit.allSourceU,
      ``TNLean.Lattice.PartyCircuit.SourceCircuit.allSourceV,
      ``TNLean.Lattice.PartyCircuit.SourceCircuit.allSourceLabels,
      ``TNLean.Lattice.PartyCircuit.SourceCircuit.allSourceBasis,
      ``TNLean.Lattice.PartyCircuit.SourceCircuit.actualSourceInputBasis,
      ``TNLean.Lattice.PartyCircuit.SourceCircuit.partialSourceGlobalMatrix,
      ``TNLean.Lattice.PartyCircuit.SourceCircuit.actualSourceInputBasis_apply,
      ``TNLean.Lattice.PartyCircuit.SourceCircuit.partialSourceGlobalMatrix_eq_toMatrix] do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

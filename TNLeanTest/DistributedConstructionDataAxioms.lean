/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.DistributedConstruction
import TNLean.Lattice.Compression.GateMapConstruction
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom checks for common original data and the two original operator descriptions -/

set_option linter.hashCommand false
open TNLean.Lattice.PartyCircuit

run_cmd do
  let declarations := #[``DistributedConstructionData, ``DistributedConstruction,
    ``DistributedConstruction.input, ``DistributedConstruction.physicalDensity,
    ``GateMapConstruction, ``GateMapConstruction.input, ``GateMapConstruction.physicalDensity]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in declarations do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

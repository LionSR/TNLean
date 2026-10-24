/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.PartyCircuit.PartyTensorMaps
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom check for tensor-map transport under equal memory spaces -/

set_option linter.hashCommand false

run_cmd do
  let decl := ``TNLean.Lattice.PartyCircuit.mapL_heq
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  unless env.contains decl do
    throwError "Missing declaration {decl}"
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.GateReexpansion
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom checks for changing the monomial lists of a fixed chronology -/

set_option linter.hashCommand false
open TNLean.PEPS.PairEffect.EffectCircuit

run_cmd do
  let declarations := #[``GateLists, ``reexpand, ``reexpandGateMaps,
    ``evalWithGateMaps_reexpand, ``reexpandLocationsEquiv, ``participants_reexpand,
    ``expandedGateCount_reexpand, ``participationCount_reexpand]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in declarations do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

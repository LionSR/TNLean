/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.EffectCircuitTermwiseCoefficientBounds
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom checks for original termwise coefficient bounds of approximate lists -/

set_option linter.hashCommand false

open TNLean.Lattice.PartyCircuit.EffectCircuit

run_cmd do
  let decls := #[``IsTermwiseBounded, ``isExpansionBounded_of_isTermwiseBounded,
    ``exists_one_le_isExpansionBounded_of_termwise_power_bounds]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in decls do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

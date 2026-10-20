/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.ActualNetworkResourceCoupling
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom checks for original resources of the actual sampled contraction -/

set_option linter.hashCommand false

run_cmd do
  let decls := #[
    ``TNLean.PEPS.PairEffect.SourceCircuit.card_alphabet_source_density_le_of_power_bounds,
    ``TNLean.PEPS.PairEffect.OriginalCircuit.card_physicalFirstDensityAlphabet_le_power,
    ``TNLean.PEPS.PairEffect.OriginalCircuit.card_incidentPhysicalFirstDensityLinks_le,
    ``TNLean.PEPS.PairEffect.OriginalCircuit.exists_original_gate_of_physicalFirst_density_link]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in decls do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

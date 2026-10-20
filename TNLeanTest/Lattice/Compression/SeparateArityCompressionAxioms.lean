/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.SeparateArityCompression
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the named declarations. -/

open TNLean.PEPS.PairEffect

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``TNLean.PEPS.Approximation.card_incidentDistributedLinks_le,
    ``TNLean.PEPS.Approximation.card_incidentDistributedLinks_le_of_arity_lifetime,
    ``SourceCircuit.card_incidentSourceDensityLinks_le_of_arity_lifetime,
    ``OriginalCircuit.card_incidentPhysicalFirstDensityLinks_le_of_arity_lifetime,
    ``OriginalCircuit.card_participants_produce_le_of_arity,
    ``DistributedConstruction.exists_uniform_sampled_network_of_arity_lifetime,
    ``DistributedConstruction.exists_uniform_sampled_network_sub_pure_le_of_arity_lifetime]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

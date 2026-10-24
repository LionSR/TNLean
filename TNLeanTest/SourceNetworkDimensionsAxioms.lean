/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.SourceNetworkDimensions
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom checks for source density link dimensions and locality -/

set_option linter.hashCommand false
open TNLean.Lattice.PartyCircuit.SourceCircuit

run_cmd do
  let decl := ``card_alphabet_source_density
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  unless env.contains decl do
    throwError "Missing declaration {decl}"
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"

run_cmd do
  let decl := ``card_alphabet_source_density_le
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  unless env.contains decl do
    throwError "Missing declaration {decl}"
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"

run_cmd do
  let decl := ``distributedLinkParties_source_subset
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  unless env.contains decl do
    throwError "Missing declaration {decl}"
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"

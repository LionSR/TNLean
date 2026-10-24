/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.CompressedBlockColumn
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Presence and permitted-axiom checks for useful compressed columns

The named declarations are required to be present, and their collected axioms
are required to belong to the standard set consisting of propositional extensionality,
classical choice and quotient soundness. Each declaration and its axioms are reported.
-/

open TNLean.Lattice.Compression.DistributedOperatorContraction

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
      ``exists_useful_column_of_sub_pure_le,
      ``TNLean.MPS.AreaLaw.ChainSweep.exists_uniform_sampled_block_column] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

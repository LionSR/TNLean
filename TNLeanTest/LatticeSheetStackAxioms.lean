/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Sheet.SheetStack
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom guard for stacks of sheets without holes

The initial step for sheets and the register and reordering facts used by the one-dimensional
protocol must exist in the production modules and depend only on standard logical axioms.
-/

set_option linter.hashCommand false

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in #[``TNLean.Lattice.Sheet.exists_originalCircuit_initial_of_owner,
      ``TNLean.Lattice.Sheet.finiteDimensional_of_mem_stackRegs,
      ``TNLean.Lattice.perm_map_cons,
      ``TNLean.Lattice.perm_map_update_cons] do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

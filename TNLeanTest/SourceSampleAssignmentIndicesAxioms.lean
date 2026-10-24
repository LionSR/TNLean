/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.SourceSampleAssignmentIndices
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom checks for common sample assignments and their finite sums -/

set_option linter.hashCommand false

open TNLean.Lattice.PartyCircuit.SourceCircuit

run_cmd do
  let decls := #[``allSourceSampleAssignmentEquiv,
    ``allSourceSampleAssignmentEquiv_symm_apply, ``sum_sourceSampleAssignments_eq]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in decls do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

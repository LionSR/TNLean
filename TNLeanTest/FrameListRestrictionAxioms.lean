/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.FrameListRestriction
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom checks for restriction of framed source-free words -/

set_option linter.hashCommand false

run_cmd do
  let decls := #[
    ``TNLean.Lattice.PartyCircuit.Word.restrict_frameList_eval_heq,
    ``TNLean.Lattice.PartyCircuit.Word.restrict_frameList_eval_heq_of_eq_nil]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in decls do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

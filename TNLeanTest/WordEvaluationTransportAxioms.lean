/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.PartyCircuit.WordEvaluationTransport
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom checks for composition and framing under equal register lists -/

set_option linter.hashCommand false

run_cmd do
  let decls := #[``TNLean.Lattice.PartyCircuit.Word.eval_comp_heq,
    ``TNLean.Lattice.PartyCircuit.Word.eval_frame_heq,
    ``TNLean.Lattice.PartyCircuit.Word.eval_frameList_heq,
    ``TNLean.Lattice.PartyCircuit.Word.eval_id_heq,
    ``TNLean.Lattice.PartyCircuit.Word.restrict_castInput_eval_heq]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in decls do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

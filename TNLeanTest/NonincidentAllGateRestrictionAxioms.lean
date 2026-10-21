/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.NonincidentAllGateRestriction
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom check for the all-party gate restriction at a nonparticipating party -/

set_option linter.hashCommand false

open TNLean.PEPS.PairEffect.SourceCircuit

run_cmd do
  let decl := ``restrict_partialWord_all_gate_localPart_eval_heq_id_of_nonincident
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  unless env.contains decl do
    throwError "Missing declaration {decl}"
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"

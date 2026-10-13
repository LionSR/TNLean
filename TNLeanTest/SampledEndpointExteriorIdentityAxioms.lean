/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SampledEndpointExteriorIdentity
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom checks for the actual sampled exterior identities -/

set_option linter.hashCommand false

open TNLean.PEPS.PairEffect.SourceCircuit in
run_cmd do
  let decls := #[``sampledEndpointWord_none_eval_heq_id,
    ``sampledEndpointInputWord_none_eval_heq_id]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in decls do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

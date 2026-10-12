/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourcePrivatePreparationRestriction
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom guard for the exterior restriction of private preparation

The selector and preparation identities must exist in the production modules
and depend only on the standard logical axioms.
-/

set_option linter.hashCommand false

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in #[
    ``TNLean.PEPS.PairEffect.partySelector_none,
    ``TNLean.PEPS.PairEffect.SourceCircuit.restrict_sourcePrivatePreparation_none_eval_heq_id] do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

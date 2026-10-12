/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.LocalPartSpectatorOwnerExclusion
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom check for spectator restriction at an excluded owner -/

set_option linter.hashCommand false

run_cmd do
  let decls := #[
    ``TNLean.PEPS.PairEffect.Word.restrict_localPart_appendTail_eval_heq_id_of_not_mem_parties,
    ``TNLean.PEPS.PairEffect.Word.restrict_localPart_mapOwner_appendTail_eval_heq_id_of_disjoint
  ]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in decls do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

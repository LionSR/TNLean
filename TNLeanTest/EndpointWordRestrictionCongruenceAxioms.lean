/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.EndpointWordRestrictionCongruence
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom check for pointwise congruence of restricted endpoint operators -/

set_option linter.hashCommand false

open TNLean.PEPS.PairEffect.SourceInventory in
run_cmd do
  let decls := #[``TNLean.PEPS.PairEffect.Word.restrict_castLayouts,
    ``restrict_endpointWord_eval_eq_of_local_eq]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in decls do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

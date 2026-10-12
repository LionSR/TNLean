/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.AbsorbedRestriction
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom guard for successive restrictions of source-free words

The word identity, its evaluation identity and the singleton specialization
must exist in the production module and depend only on standard logical axioms.
-/

set_option linter.hashCommand false

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in #[``TNLean.PEPS.PairEffect.Word.restrict_restrict_heq_of_implies,
      ``TNLean.PEPS.PairEffect.Word.restrict_restrict_eval_heq_of_implies,
      ``TNLean.PEPS.PairEffect.Word.restrict_withoutParty_atParty_eval_heq] do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

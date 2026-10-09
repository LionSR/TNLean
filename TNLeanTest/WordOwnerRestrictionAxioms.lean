/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.WordOwnerRestriction
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Kernel dependencies of source-free owner restrictions

Check the two owner-restriction identities and the generic party selector in the
imported library. Every named declaration must exist, and every transitive axiom
dependency must be one of `propext`, `Classical.choice` and `Quot.sound`. A
declaration may use any subset of these axioms, including the empty set.
-/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in #[``TNLean.PEPS.PairEffect.Word.parties_mapOwner_of_sources_nil,
      ``TNLean.PEPS.PairEffect.Word.restrict_mapOwner_eval_eq_id_of_disjoint,
      ``TNLean.PEPS.PairEffect.partySelector] do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

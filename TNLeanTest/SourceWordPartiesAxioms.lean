/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceWordParties
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom guards for participating parties of sourceful words

The two party-set identities and their exterior restriction consequence must
exist and depend only on the standard logical axioms.
-/

open TNLean.PEPS.PairEffect.Word in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in #[``parties_localPart, ``parties_mapOwner,
      ``restrict_localPart_mapOwner_eval_heq_id_of_disjoint] do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

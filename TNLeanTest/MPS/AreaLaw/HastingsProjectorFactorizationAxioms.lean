/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.ProjectorFactorization
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for Lemma 1 of Hastings' area law on the chain. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``TNLean.MPS.AreaLaw.Hastings.lemmaOne_errorBudget,
    ``Matrix.IsGappedGroundState.sub_smul_one,
    ``TNLean.MPS.AreaLaw.isFactorizationAt_zero_one_one,
    ``TNLean.MPS.AreaLaw.exists_isFactorizationAt_sqrt_decay,
    ``TNLean.MPS.AreaLaw.exists_projectorFactorization,
    ``TNLean.MPS.AreaLaw.exists_projectorFactorization_posSemidef] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

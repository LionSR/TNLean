/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.LemmaOneConstant
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the polynomial bound on the constant of Lemma 1 of
Hastings' area law. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``TNLean.MPS.AreaLaw.Hastings.lemmaOneBudgetA,
    ``TNLean.MPS.AreaLaw.Hastings.lemmaOneBudgetB,
    ``TNLean.MPS.AreaLaw.lemmaOneSqrtA,
    ``TNLean.MPS.AreaLaw.lemmaOneSqrtB,
    ``TNLean.MPS.AreaLaw.lemmaOneConst,
    ``TNLean.MPS.AreaLaw.lemmaOneConst_nonneg,
    ``TNLean.MPS.AreaLaw.exists_isFactorizationAt_lemmaOneConst,
    ``TNLean.MPS.AreaLaw.sixteen_le_lemmaOneLength_and_le,
    ``TNLean.MPS.AreaLaw.lemmaOneConst_le_pow,
    ``TNLean.MPS.AreaLaw.exists_projectorFactorization_pow] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

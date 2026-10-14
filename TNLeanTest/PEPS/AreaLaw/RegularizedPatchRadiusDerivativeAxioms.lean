/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RegularizedPatchRadiusDerivative
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Audit the ordered output derivative and its conditional logarithmic norm formula. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.PEPS.hasDerivAt_regularizedPatchOutput_exp_neg,
      ``TNLean.PEPS.hasDerivAt_log_regularizedPatchObjective_exp_neg_of_outer_commute] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

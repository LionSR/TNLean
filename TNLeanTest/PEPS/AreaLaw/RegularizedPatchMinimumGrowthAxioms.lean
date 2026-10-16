/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RegularizedPatchMinimumGrowth
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Logical dependencies of the original patch-minimum estimates -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.PEPS.log_regularizedPatchMinimum_exp_neg_le_of_regulator_trace,
      ``TNLean.PEPS.log_regularizedPatchMinimum_exp_neg_le_of_entropy_distance] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

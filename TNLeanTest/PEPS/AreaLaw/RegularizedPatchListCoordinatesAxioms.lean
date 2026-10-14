/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RegularizedPatchListCoordinates
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Audit the ordered patch output, objective, minimization comparison and
normalization under the canonical configuration identification. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.PEPS.dependentGlobalConfigIsometry_regularizedPatchOutput,
      ``TNLean.PEPS.regularizedPatchObjective_eq_norm_patchOutput,
      ``TNLean.PEPS.isPatchMinimizer_regularizedPatchFactorList,
      ``TNLean.PEPS.dependentGlobalConfigIsometry_normalizedRegularizedPatchOutput] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

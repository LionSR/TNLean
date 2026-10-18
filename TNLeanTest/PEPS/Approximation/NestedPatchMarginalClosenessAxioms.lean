/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.NestedPatchMarginalCloseness
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Audit uniform marginal approximation at an actual nested-patch minimum. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in #[``TNLean.PEPS.Approximation.nestedPatch_minimizer_marginal_closeness,
      ``TNLean.PEPS.Approximation.exists_uniform_nestedPatch_minimizer_marginal_closeness] do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

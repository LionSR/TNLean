/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.PatchEnergySmallnessScale
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Named standard-axiom check for the filter exponent of the patch construction. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in #[``TNLean.PEPS.patchFilterExponent,
      ``TNLean.PEPS.patchFilterExponent_le_half,
      ``TNLean.PEPS.patchFilterExponent_pos,
      ``TNLean.PEPS.patchFilterExponent_pos_of_pos,
      ``TNLean.PEPS.mul_sq_le_div_1024_of_le_patchFilterExponent,
      ``TNLean.PEPS.mul_patchFilterExponent_sq_le] do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

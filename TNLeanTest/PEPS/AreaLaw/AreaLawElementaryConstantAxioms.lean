/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.AreaLawElementaryConstant
import Lean.Util.CollectAxioms

/-! # Kernel dependencies of the area law with a constant that iterates no recursion -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.PEPS.AreaLaw.physicalBoxConstantElementary,
      ``TNLean.PEPS.AreaLaw.physicalBoxConstantClosed_le_elementary,
      ``TNLean.PEPS.AreaLaw.uniformAreaLawConstantElementary,
      ``TNLean.PEPS.AreaLaw.uniformAreaLaw_elementary] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

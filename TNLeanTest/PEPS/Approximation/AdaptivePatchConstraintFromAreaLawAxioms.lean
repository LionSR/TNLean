/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.AdaptivePatchConstraintFromAreaLaw
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Audit the adaptive patch constraint from the square entropy area law. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in #[``TNLean.PEPS.Approximation.adaptivePatchPrefactor_pos,
      ``TNLean.PEPS.Approximation.adaptivePatchExponent_pos,
      ``TNLean.PEPS.Approximation.SquareEntropyAreaLawAt.adaptivePatchSupply,
      ``TNLean.PEPS.Approximation.SquareEntropyAreaLaw.adaptivePatchConstraint] do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

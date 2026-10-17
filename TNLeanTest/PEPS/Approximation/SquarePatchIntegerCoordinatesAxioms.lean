/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SquarePatchIntegerCoordinates
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Audit square samples and physical lattice coordinates. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.PEPS.Approximation.squareSample_integerCoordinates,
      ``TNLean.PEPS.Approximation.integerCoordinates_add_one_eq_latticePos] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

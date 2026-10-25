/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.EntropyScaling.VonNeumannObstruction
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Axiom audits for the von Neumann entropy obstruction to efficient approximation. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in
      #[``TNLean.MPS.AreaLaw.IsEfficientlyApproximableByMPS.exists_vonNeumann_bound,
        ``TNLean.MPS.AreaLaw.not_isEfficientlyApproximableByMPS_of_linear_vonNeumann_growth] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

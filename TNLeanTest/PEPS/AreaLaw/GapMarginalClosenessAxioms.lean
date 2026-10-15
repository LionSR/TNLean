/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.GapMarginalCloseness
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Audit the full-system gap bound and its one-sixteenth energy criterion. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``FiniteProduct.re_trace_abs_reducedPure_sub_le_sqrt_energy,
      ``FiniteProduct.re_trace_abs_reducedPure_sub_le_one_sixteenth_of_energy] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

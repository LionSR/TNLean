/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.MPSApproximation
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Axiom audits for the accuracy-dependent chain MPS approximation theorem and
its fixed-accuracy specialization. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.MPS.AreaLaw.exists_isOpenMPS_norm_sub_le_of_error,
      ``TNLean.MPS.AreaLaw.exists_isOpenMPS_norm_sub_le,
      ``TNLean.MPS.AreaLaw.exists_isOpenMPS_norm_sub_le_of_error_rpow,
      ``TNLean.MPS.AreaLaw.ChainHamiltonian.spectralProjectionGE_leftBlock_bounds] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

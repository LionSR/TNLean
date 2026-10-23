/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.MPSFromEntropy
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the matrix product state approximation from the
entropy of the cuts in Hastings' section on matrix product states. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
      ``TNLean.MPS.AreaLaw.Hastings.isOpenMPS_norm_sub_sq_le_of_factorization_of_entropy,
      ``TNLean.MPS.AreaLaw.Hastings.isOpenMPS_norm_sub_sq_le_of_isFactorizationAt_of_entropy] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

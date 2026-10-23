/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.BoundaryLocalization
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the localization of the boundary operator `P_B`
in Hastings' Lemma 1. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``TNLean.MPS.AreaLaw.Hastings.norm_interactionPropagator_sub_le,
    ``TNLean.MPS.AreaLaw.Hastings.exists_supported_interactionAverage_approx,
    ``TNLean.MPS.AreaLaw.Hastings.exists_supported_interactionAverage_approx_exp] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

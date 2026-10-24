/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.ProjectorFactorizationScaling
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for Lemma 1 of Hastings' area law in units of the gap. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``Entropy.IsSupportedOn.smul,
    ``Matrix.IsGappedGroundState.smul,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.smul,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.smul_operator,
    ``TNLean.MPS.AreaLaw.lemmaOneLength_div,
    ``TNLean.MPS.AreaLaw.exists_projectorFactorization_div] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

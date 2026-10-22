/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.ChainLocalizedParts
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the localized filtered parts `M_L`, `M_B`, `M_R`
of the chain Hamiltonian in Hastings' Lemma 1. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``TNLean.MPS.AreaLaw.isSupportedOn_localized_sub_self,
    ``TNLean.MPS.AreaLaw.isHermitian_localized,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.norm_gaussianFilteredTerm_sub_localized_le_of_commutator,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.norm_gaussianFilteredTerm_leftPart_sub_localized_le,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.norm_gaussianFilteredTerm_rightPart_sub_localized_le,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.norm_gaussianFilteredTerm_bufferPart_sub_localized_le,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.isHermitian_leftPart_localized,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.isHermitian_rightPart_localized,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.isHermitian_bufferPart_localized,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.leftPart_eq_zero_of_le] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

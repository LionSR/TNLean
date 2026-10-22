/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.PartCommutators
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the commutators of the parts `H_L`, `H_B`, `H_R`
with the chain Hamiltonian in Hastings' Lemma 1. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.commutator_leftPart_eq,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.norm_commutator_leftPart_le,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.isSupportedOn_commutator_leftPart,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.norm_commutator_rightPart_le,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.isSupportedOn_commutator_rightPart,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.norm_commutator_bufferPart_le,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.isSupportedOn_commutator_bufferPart] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

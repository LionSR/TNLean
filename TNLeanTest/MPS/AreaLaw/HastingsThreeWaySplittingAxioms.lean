/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.ThreeWaySplitting
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the three-way splitting of a chain Hamiltonian at
a cut, the first step of the proof of Hastings' Lemma 1. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.operator_eq_leftPart_add_bufferPart_add_rightPart,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.groundCentered_parts_sum_of_eigen,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.isGappedGroundState_groundCentered_parts_sum,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.isSupportedOn_leftPart,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.isSupportedOn_rightPart,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.isSupportedOn_bufferPart,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.norm_bufferPart_le,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.norm_groundCentered_bufferPart_le,
    ``TNLean.MPS.AreaLaw.Hastings.inner_groundCentered] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

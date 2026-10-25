/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.CutoffPair
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the cut-offs `O_L`, `O_R` of Lemma 1 in Hastings'
area law. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``TNLean.Lattice.norm_gaussianFilteredTerm_sub_self_le,
    ``TNLean.MPS.AreaLaw.chainNeighborhood_interval_subset,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.isSupportedOn_localizedPart_leftPart,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.isSupportedOn_localizedPart_rightPart,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.norm_localizedPart_apply_le,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.exists_cutoffPair] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

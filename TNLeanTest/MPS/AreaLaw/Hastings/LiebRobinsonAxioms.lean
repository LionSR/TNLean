/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.LiebRobinson
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-foundation checks for Hastings' numerical chain commutator estimate,
physical-time rescaling, and the factorization lengths. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``QuantumCircuit.heisenbergEvolution_smul,
    ``QuantumCircuit.heisenbergEvolution_inv_smul_mul,
    ``TNLean.MPS.AreaLaw.ChainSupport.edist_le,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.norm_heisenberg_commutator_le_numeric,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.norm_heisenberg_commutator_le_hastings,
    ``TNLean.MPS.AreaLaw.chainLRVelocity_sub_one_pos,
    ``TNLean.MPS.AreaLaw.two_mul_lemmaOneEndpointLength_le_sourceLength,
    ``TNLean.MPS.AreaLaw.lemmaOneLength_eq_sourceLength,
    ``TNLean.MPS.AreaLaw.lemmaOneEndpointLength_eq_sourceLength,
    ``TNLean.MPS.AreaLaw.chainLRVelocity_gapRescaling,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.norm_heisenberg_commutator_le_hastings_rescaled] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

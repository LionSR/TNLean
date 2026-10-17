/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SquareZeroFloorOptimizer
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Audit the physical same-family energy and full-system fidelity theorem. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``TNLean.PEPS.Approximation.SquareHamiltonian.exists_zero_floor_maximizer_energy_fidelity,
    ``TNLean.PEPS.Approximation.SquareHamiltonian.exists_nearestNeighbor_terms,
    ``TNLean.PEPS.Approximation.SquareHamiltonian.isGappedGroundState_toAreaLawHamiltonian,
    ``TNLean.PEPS.AreaLaw.nearestNeighbor_crossing_budget,
    ``Entropy.exists_max_feasible_chain_zero_floor_normalized_abs_energy_sharp]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

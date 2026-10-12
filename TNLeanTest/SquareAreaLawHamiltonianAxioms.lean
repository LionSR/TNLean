/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SquareAreaLawHamiltonian
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Audit the actual square-to-integer-domain Hamiltonian conversion. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``TNLean.PEPS.Approximation.squareAreaLawSupport,
    ``TNLean.PEPS.Approximation.squareAreaLawSupport_injective,
    ``TNLean.PEPS.Approximation.squareAreaLawState,
    ``TNLean.PEPS.Approximation.norm_squareAreaLawState,
    ``TNLean.PEPS.Approximation.SquareHamiltonian.hermitianTerm_mem_supportedOperators,
    ``TNLean.PEPS.Approximation.SquareHamiltonian.toAreaLawHamiltonian,
    ``TNLean.PEPS.Approximation.SquareHamiltonian.toAreaLawHamiltonian_operator,
    ``TNLean.PEPS.Approximation.SquareHamiltonian.isGappedGroundState_toAreaLawHamiltonian]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

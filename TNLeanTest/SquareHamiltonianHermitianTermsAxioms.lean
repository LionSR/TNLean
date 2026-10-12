/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SquareHamiltonianHermitianTerms
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Audit the original square interaction labels and their Hermitian replacement. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``TNLean.PEPS.Approximation.SquareInteraction,
    ``TNLean.PEPS.Approximation.squareInteractionSupport,
    ``TNLean.PEPS.Approximation.SquareHamiltonian.hermitianTerm,
    ``TNLean.PEPS.Approximation.SquareHamiltonian.hermitianTerm_supported,
    ``TNLean.PEPS.Approximation.SquareHamiltonian.hermitianTerm_isHermitian,
    ``TNLean.PEPS.Approximation.SquareHamiltonian.hermitianTerm_norm_le,
    ``TNLean.PEPS.Approximation.SquareHamiltonian.sum_hermitianTerm]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

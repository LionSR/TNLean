/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/

import TNLean.PEPS.Approximation.InformationReset
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# The information reset with explicit constants: axiom checks

The imported declarations use only propositional extensionality, classical
choice, and quotient soundness.
-/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[
    ``TNLean.Lattice.regional_physicalBuffer_filter,
    ``TNLean.PEPS.Approximation.SquareHamiltonian.reset_localized_filter,
    ``TNLean.PEPS.Approximation.SquareHamiltonian.reset_unitary,
    ``TNLean.PEPS.Approximation.SquareHamiltonian.information_reset_of_resetThreshold_le,
    ``TNLean.PEPS.Approximation.SquareHamiltonian.information_reset,
    ``TNLean.PEPS.Approximation.resetWidth_eq,
    ``TNLean.PEPS.Approximation.resetUnitaryPrefactor_eq]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

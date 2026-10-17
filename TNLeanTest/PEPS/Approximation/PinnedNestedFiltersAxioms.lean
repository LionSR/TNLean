/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PinnedZeroFloorOptimizer
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-only logical dependencies for the complete adapted-filter comparison. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``TNLean.PEPS.Approximation.Pinned.liftLocal_eq_localLift,
    ``TNLean.PEPS.Approximation.Pinned.NestedFilter.canonicalMatrices_fromCanonical,
    ``TNLean.PEPS.Approximation.Pinned.NestedFilter.fromCanonical_canonicalMatrices,
    ``TNLean.PEPS.Approximation.Pinned.NestedFilter.admissible_iff_feasible,
    ``TNLean.PEPS.Approximation.Pinned.NestedFilter.squareAreaLawState_output,
    ``TNLean.PEPS.Approximation.Pinned.NestedFilter.squareAreaLawState_normalizedOutput,
    ``TNLean.PEPS.Approximation.Pinned.NestedFilter.isMaximizer_iff,
    ``TNLean.PEPS.Approximation.Pinned.NestedFilter.Energy.card_edgeBoundary_eq_crossingCount,
    ``TNLean.PEPS.Approximation.SquareHamiltonian.exists_pinned_maximizer_energy_fidelity]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

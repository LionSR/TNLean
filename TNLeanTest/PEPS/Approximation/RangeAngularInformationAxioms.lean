/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/

import TNLean.PEPS.Approximation.RangeAngularInformation
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Angular information at range `R`: axiom checks

The imported declarations use only propositional extensionality, classical
choice, and quotient soundness.
-/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[
    ``TNLean.PEPS.Approximation.isAngularScale_of_bounds,
    ``TNLean.PEPS.Approximation.IsRangeSquareGroundState.squareCellInformationBound,
    ``TNLean.PEPS.Approximation.IsRangeSquareGroundState.squareResetBound,
    ``TNLean.PEPS.Approximation.rangeAngularScale_eq,
    ``TNLean.PEPS.Approximation.isAngularScale_range_closed_le]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

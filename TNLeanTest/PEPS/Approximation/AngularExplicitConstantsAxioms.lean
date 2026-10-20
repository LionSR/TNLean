/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.AngularInformationFromCollar
import TNLean.PEPS.Approximation.AngularInformationFromGap
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Axiom check for the explicit constants of Proposition 3.4

Each named theorem with explicit slope and size threshold, and each statement at the named
amplification constants or at closed-form constants, depends on exactly the three standard
axioms used throughout the library.
-/

open TNLean.PEPS.Approximation in
run_cmd do
  let decls := #[
    ``TNLean.PEPS.Approximation.reset_scale_polylog_le_of_resetPolylogScale_le,
    ``TNLean.PEPS.Approximation.angular_reset_width_bound_of_threshold_le,
    ``TNLean.PEPS.Approximation.angular_reset_width_lt_of_threshold_le,
    ``TNLean.PEPS.Approximation.angular_reset_width_lt_of_cell_information,
    ``TNLean.PEPS.Approximation.angular_information_reset_of_resetThreshold_le,
    ``mutualInformation_selectedRegion_le_square_of_sublinearCollarBoundAt,
    ``TNLean.PEPS.Approximation.angular_single_scale_reset_of_sublinearCollarBoundAt,
    ``TNLean.PEPS.Approximation.IsAngularScale.of_sitePosition,
    ``TNLean.PEPS.Approximation.angularScale_eq,
    ``TNLean.PEPS.Approximation.angularInformationBound_of_sublinearCollarBoundAt_le,
    ``TNLean.PEPS.Approximation.isAngularScale_of_sublinearCollarBoundAt_le,
    ``TNLean.PEPS.AreaLaw.amplificationBoundAt_explicit,
    ``TNLean.PEPS.Approximation.amplificationBoundAt_collarAmplification,
    ``cell_conditionalMutualInformation_le_square_of_sublinearCollarBoundAt_explicit,
    ``TNLean.PEPS.Approximation.isAngularScale_of_sublinearCollarBoundAt_le_explicit,
    ``TNLean.PEPS.Approximation.sublinearCollarBoundAt_closed,
    ``TNLean.PEPS.Approximation.coarse_mutualInformation_le_closed,
    ``TNLean.PEPS.Approximation.cell_conditionalMutualInformation_le_closed,
    ``TNLean.PEPS.Approximation.cell_conditionalMutualInformation_le_square_closed,
    ``TNLean.PEPS.Approximation.isAngularScale_closed_le]
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (expected.contains ·) && expected.all (axioms.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.TwoFamilyExplicitThresholds
import Lean.Util.CollectAxioms

/-!
# Logical dependencies of the explicit two-family thresholds

Each public theorem must exist and have precisely the three standard logical axioms.
-/

run_cmd do
  let names := #[
    `TNLean.PEPS.AreaLaw.Geometry.le_two_pow_of_dyadicIndexThreshold_le,
    `TNLean.PEPS.AreaLaw.Geometry.le_two_pow_fineScaleIndex_of_fineScaleIndexThreshold_le,
    `TNLean.PEPS.AreaLaw.Geometry.primaryScaleLimits_of_primaryScaleLimitThreshold_le,
    `TNLean.PEPS.AreaLaw.Geometry.le_primaryScannerScale_of_primaryScannerScaleThreshold_le,
    `TNLean.PEPS.AreaLaw.Geometry.fine_clearance_of_fineClearanceThreshold_le,
    `TNLean.PEPS.AreaLaw.Geometry.beltReplacementScaleLimit_of_beltReplacementScaleThreshold_le]
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in names do
    unless (← Lean.getEnv).contains decl do
      throwError "The intended threshold declaration is absent: {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (expected.contains ·) && expected.all (axioms.contains ·) do
      throwError "Unexpected logical dependencies for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

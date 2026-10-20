/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.PhysicalBoxStepBound
import Lean.Util.CollectAxioms

/-!
# Logical dependencies of the closed-form bound for the bootstrap constants

Each public declaration must exist and have precisely the three standard logical axioms.
-/

run_cmd do
  let names := #[
    `TNLean.PEPS.AreaLaw.Scan.boxBootstrapConstant_le_iterate,
    `TNLean.PEPS.AreaLaw.Scan.one_add_iterate_mul_one_add_pow_le,
    `TNLean.PEPS.AreaLaw.Scan.boxBootstrapConstant_le_pow_pow,
    `TNLean.PEPS.AreaLaw.Scan.boxStepExponent,
    `TNLean.PEPS.AreaLaw.Scan.boxStepScale,
    `TNLean.PEPS.AreaLaw.Scan.boxStepPrefactor,
    `TNLean.PEPS.AreaLaw.Scan.boxImprovementThreshold_le_add,
    `TNLean.PEPS.AreaLaw.Scan.boxBootstrapStep_le_boxStepPrefactor,
    `TNLean.PEPS.AreaLaw.Scan.physicalBoxBootstrapConstant_le_pow_pow,
    `TNLean.PEPS.AreaLaw.Scan.physicalBoxConstantExplicit_le_pow_pow]
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in names do
    unless (← Lean.getEnv).contains decl do
      throwError "The intended bootstrap declaration is absent: {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (expected.contains ·) && expected.all (axioms.contains ·) do
      throwError "Unexpected logical dependencies for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

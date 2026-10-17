/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.TwoFamilyAssembly
import Lean.Util.CollectAxioms

/-!
# Logical dependencies of the two-family decomposition

Each public theorem must exist and have precisely the three standard logical axioms.
-/

run_cmd do
  let names := #[
    `TNLean.PEPS.AreaLaw.Geometry.exists_primaryLayer_of_repairStageBirthRank_eq_zero,
    `TNLean.PEPS.AreaLaw.Geometry.exists_uniform_repairStage_primary_error_sum_bound,
    `TNLean.PEPS.AreaLaw.Geometry.card_repairStageExceptionalSites_le_of_isEmpty,
    `TNLean.PEPS.AreaLaw.twoFamilyDecomposition]
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in names do
    unless (← Lean.getEnv).contains decl do
      throwError "The intended geometric declaration is absent: {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (expected.contains ·) && expected.all (axioms.contains ·) do
      throwError "Unexpected logical dependencies for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairRankZeroAncestry
import Lean.Util.CollectAxioms

/-! # Logical dependencies of retained identifiers and their primary ancestors -/

run_cmd do
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    `TNLean.PEPS.AreaLaw.Geometry.repairStageOldInclusion_injective,
    `TNLean.PEPS.AreaLaw.Geometry.repairStageOldInclusion_dummy,
    `TNLean.PEPS.AreaLaw.Geometry.exists_repairStageOldInclusion_of_repairStageBirthRank_eq_zero,
    `TNLean.PEPS.AreaLaw.Geometry.repairStage_color_oldInclusion,
    `TNLean.PEPS.AreaLaw.Geometry.repairStageCharacteristicLength_oldInclusion,
    `TNLean.PEPS.AreaLaw.Geometry.existsUnique_initialPrimary_of_repairStageBirthRank_eq_zero
  ] do
    unless (← Lean.getEnv).contains decl do
      throwError "The intended geometric theorem is absent: {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (expected.contains ·) && expected.all (axioms.contains ·) do
      throwError "Unexpected logical dependencies for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

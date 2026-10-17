/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairRetainedNonprimaryErrorSum
import Lean.Util.CollectAxioms

/-! # Logical dependencies of the retained nonprimary error estimate -/

run_cmd do
  let decls := #[
    `TNLean.PEPS.AreaLaw.Geometry.repairStageCharacteristicLength_pos_of_ne_dummy,
    `TNLean.PEPS.AreaLaw.Geometry.exists_uniform_repairStage_retained_positive_rank_error_sum_bound]
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "The intended geometric theorem is absent: {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (expected.contains ·) && expected.all (axioms.contains ·) do
      throwError "Unexpected logical dependencies for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

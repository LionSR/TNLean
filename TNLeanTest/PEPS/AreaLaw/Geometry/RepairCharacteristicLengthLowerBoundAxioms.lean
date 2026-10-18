/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairCharacteristicLengthLowerBound
import Lean.Util.CollectAxioms

/-! # Logical dependencies of the uniform lower bound on nonprimary birth lengths -/

run_cmd do
  let names := #[
    `TNLean.PEPS.AreaLaw.Geometry.repairStage_positive_rank_length_lower_bound,
    `TNLean.PEPS.AreaLaw.Geometry.exists_uniform_repairStage_positive_rank_length_lower_bound]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in names do
    unless (← Lean.getEnv).contains decl do
      throwError "The intended characteristic-length theorem is absent: {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) && allowed.all (axioms.contains ·) do
      throwError "Unexpected logical dependencies for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

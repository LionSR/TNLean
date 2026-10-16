/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairDescendantCounts
import TNLean.PEPS.AreaLaw.Geometry.RepairTermination
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom audit for finite repair descendants and a common empty generation. -/

run_cmd do
  let decls := #[
    ``TNLean.PEPS.AreaLaw.Geometry.repairMarkParent_repairMarkOffset_injective,
    ``TNLean.PEPS.AreaLaw.Geometry.finite_repairStage_markIndex,
    ``TNLean.PEPS.AreaLaw.Geometry.repairMarkAncestor_parent_offset_injective,
    ``TNLean.PEPS.AreaLaw.Geometry.card_repairMarkAncestor_fiber_succ_le,
    ``TNLean.PEPS.AreaLaw.Geometry.card_repairMarkAncestor_fiber_le,
    ``TNLean.PEPS.AreaLaw.Geometry.RepairMetricHypotheses.exists_isEmpty_markIndex]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

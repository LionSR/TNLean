/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.WeakRectangleShellEntropy
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
Check integer dyadic rectangles, their physical entropy cover, and the
explicit-budget safe-shell estimates against the standard axioms.
-/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.PEPS.AreaLaw.Geometry.latticeDyadicRect,
      ``TNLean.PEPS.AreaLaw.Geometry.toFinset_latticeDyadicRect,
      ``TNLean.PEPS.AreaLaw.Geometry.size_latticeDyadicRect,
      ``TNLean.PEPS.AreaLaw.Geometry.rectRegion_latticeDyadicRect,
      ``TNLean.PEPS.AreaLaw.Geometry.biUnion_rectRegion_cappedDyadicPartition,
      ``TNLean.PEPS.AreaLaw.Geometry.pairwiseDisjoint_rectRegion_cappedDyadicPartition,
      ``TNLean.PEPS.AreaLaw.Geometry.regionalEntropy_filter_le_sum_rectRegion,
      ``TNLean.PEPS.AreaLaw.Geometry.regionalEntropy_filter_le_weighted_cover,
      ``TNLean.PEPS.AreaLaw.IsSafe.isSafe_cappedDyadicPartition_shell,
      ``TNLean.PEPS.AreaLaw.IntRect.regionalEntropy_shell_le_of_safe_box] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

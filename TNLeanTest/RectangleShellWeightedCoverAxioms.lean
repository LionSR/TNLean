/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RectangleShellWeightedCover
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
Check finite dyadic summation and the weighted rectangle shell estimate
against the standard axioms.
-/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.PEPS.AreaLaw.Geometry.sum_weighted_dyadic_rpow_le,
      ``TNLean.PEPS.AreaLaw.Geometry.sum_cappedDyadicPartition_by_scale,
      ``TNLean.PEPS.AreaLaw.IntRect.sum_rpow_cappedDyadicPartition_shell_le] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

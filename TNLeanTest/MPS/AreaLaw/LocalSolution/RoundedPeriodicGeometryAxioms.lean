/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.RoundedPeriodicGeometry
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Kernel-axiom checks for rounded physical-chain geometry. -/

open TNLean.MPS.AreaLaw.LocalSolution

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``roundedPeriodicBlock,
      ``roundedPeriodicEdge,
      ``roundedPeriodicDistance,
      ``roundedPeriodicBlock_lt,
      ``roundedPeriodicEdge_internal_centre,
      ``roundedPeriodicEdge_support,
      ``roundedPeriodicBlockCount,
      ``roundedPeriodicBlockCount_pos,
      ``roundedPeriodicBlockCount_cover,
      ``roundedPeriodicBlockCount_upper,
      ``roundedPeriodicBlockCount_le,
      ``roundedPeriodicEdge_support_of_cover,
      ``roundedPeriodicEdge_zero_support] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.FinalStateEnergy
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and dependency checks for the energy of every final hierarchical state. -/

open TNLean.MPS.AreaLaw.LocalSolution

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``abs_re_inner_sub_le_of_windowProjection,
    ``abs_re_inner_sub_le_of_compressedWindowProjection, ``isStarProjection_hierarchy,
    ``abs_re_inner_hierarchySum_sub_le, ``re_inner_hierarchySum_le_add,
    ``card_le_two_mul_re_trace_of_hierarchy, ``hierarchySum_one] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

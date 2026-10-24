/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.SupersiteFinalState
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and dependency checks for the final states of the hierarchy on supersites. -/

open TNLean.MPS.AreaLaw.LocalSolution

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``commute_supersiteHierarchy, ``isStarProjection_supersiteHierarchy,
    ``abs_re_inner_supersiteHierarchySum_sub_le, ``re_inner_supersiteHierarchySum_le_add,
    ``card_le_two_mul_re_trace_of_supersiteHierarchy, ``norm_sub_supersiteClosingLinkWindow_le,
    ``re_inner_supersiteHierarchySum_add_le_add,
    ``card_le_two_mul_re_trace_of_supersiteClosingLink] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

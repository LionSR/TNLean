/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.HierarchyNesting
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Foundation checks for the retained spaces of every node of the hierarchy. -/

open TNLean.MPS.AreaLaw.LocalSolution

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``toEuclideanLin_eq_of_mul_eq, ``IsRetainedHierarchy,
      ``hierarchyProjection_children, ``isRetainedHierarchy_of_hierarchyProjection,
      ``isRetainedHierarchy_of_hierarchyClosingProjection] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

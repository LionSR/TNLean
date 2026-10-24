/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.HierarchyLevels
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the deficiencies of all levels of Hastings'
hierarchical projection. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``TNLean.MPS.AreaLaw.LocalSolution.norm_sub_compressedWindowProjection_mul_sq_le,
    ``TNLean.MPS.AreaLaw.LocalSolution.hierarchyDeficiency,
    ``TNLean.MPS.AreaLaw.LocalSolution.norm_sub_hierarchy_le,
    ``TNLean.MPS.AreaLaw.LocalSolution.hierarchyMajorant,
    ``TNLean.MPS.AreaLaw.LocalSolution.hierarchyMajorant_nonneg,
    ``TNLean.MPS.AreaLaw.LocalSolution.hierarchyDeficiency_le_hierarchyMajorant,
    ``TNLean.MPS.AreaLaw.LocalSolution.hierarchyMajorant_le] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

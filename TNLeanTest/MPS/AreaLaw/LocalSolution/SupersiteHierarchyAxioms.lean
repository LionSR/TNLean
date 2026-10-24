/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.SupersiteHierarchy
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the supersite grouping of Hastings' hierarchical
projection. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``TNLean.MPS.AreaLaw.LocalSolution.cfc_mem_supportedOperators,
    ``TNLean.MPS.AreaLaw.LocalSolution.windowProjection_mem_supportedOperators,
    ``TNLean.MPS.AreaLaw.LocalSolution.compressedWindowProjection_mem_supportedOperators,
    ``TNLean.MPS.AreaLaw.LocalSolution.levelBlock,
    ``TNLean.MPS.AreaLaw.LocalSolution.levelBlock_two_mul_subset,
    ``TNLean.MPS.AreaLaw.LocalSolution.levelBlock_two_mul_add_one_subset,
    ``TNLean.MPS.AreaLaw.LocalSolution.disjoint_levelBlock_two_mul,
    ``TNLean.MPS.AreaLaw.LocalSolution.mem_supportedOperators_hierarchy,
    ``TNLean.MPS.AreaLaw.LocalSolution.norm_sub_supersiteHierarchy_le,
    ``TNLean.MPS.AreaLaw.LocalSolution.norm_toEuclideanLin_sum_sub_le] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.GaussianFilteredTruncationWeighted
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Kernel-axiom checks for the weighted omitted-interaction truncation estimates. -/

open TNLean.Lattice

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``norm_gaussianFilteredTerm_sub_truncated_le_of_commutator_bounds,
      ``norm_commutator_heisenbergEvolution_le_anchor_kernel,
      ``norm_gaussianFilteredTerm_sub_truncated_le_anchor_sum,
      ``norm_gaussianFilteredTerm_sub_truncated_le_degree_tail] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

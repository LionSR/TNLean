/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.GaussianFilteredTermLocalization
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Logical dependencies of the locality of Gaussian-filtered terms on a finite graph. -/

open TNLean.Lattice

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``isHermitian_gaussianFilteredTerm,
      ``norm_commutator_gaussianFilteredTerm_le_graphDistance,
      ``norm_gaussianFilteredTerm_sub_siteExpectation_le_graphNeighborhood,
      ``exists_local_approx_gaussianFilteredTerm,
      ``norm_sub_starProjection_apply_le_of_gaussianFilteredTerm,
      ``norm_apply_sub_inner_smul_le_of_gaussianFilteredTerm,
      ``norm_sum_sub_le_of_sum_eq] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.LowEnergyCommutator
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Logical dependencies of the low-energy commutators of Gaussian-filtered terms. -/

open TNLean.Lattice

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``groundCompression_gaussianFilteredTerm,
      ``norm_one_sub_starProjection_mul_gaussianFilteredTerm_mul_le,
      ``norm_starProjection_mul_gaussianFilteredTerm_mul_one_sub_le,
      ``norm_groundCompression_commutator_le,
      ``norm_commutator_gaussianFilteredTerm_le_of_disjoint,
      ``norm_groundCompression_commutator_le_graphNeighborhood,
      ``abs_sub_mul_norm_inner_le_norm_commutator,
      ``norm_inner_le_norm_commutator_div] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

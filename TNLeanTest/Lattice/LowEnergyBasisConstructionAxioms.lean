/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.LowEnergyBasisConstruction
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Kernel-axiom checks for the constructed ground-space basis and its summed estimate. -/

open TNLean.Lattice

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``quotientConditionNumber, ``compressionConditionNumber,
      ``norm_le_quotientConditionNumber_mul,
      ``exists_orthonormalBasis_joint_eigenvectors, ``finrank_selfAdjoint_continuousLinearMap,
      ``exists_orthonormalBasis_norm_inner_le_compressionCommutatorMap,
      ``exists_orthonormalBasis_norm_inner_le_commutators,
      ``isSelfAdjoint_groundSpaceCompression, ``norm_groundSpaceCompression_le,
      ``norm_groundSpaceCompression_commutator_le,
      ``norm_groundSpaceCompression_eq, ``norm_groundSpaceCompression_commutator_eq,
      ``exists_groundSpaceBasis_sum_norm_offDiagonalPartFamily_le] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

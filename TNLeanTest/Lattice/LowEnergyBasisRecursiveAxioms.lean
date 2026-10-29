/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.LowEnergyBasisRecursive
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Kernel-axiom checks for the actual recursive uniform ground-space basis construction. -/

open TNLean.Lattice

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``norm_subspaceCompression_commutator,
      ``isSelfAdjoint_subspaceCompression,
      ``exists_orthonormalBasis_orthogonal_sum,
      ``exists_orthonormalBasis_orthogonal_sum_fin,
      ``norm_inner_le_of_orthogonal_sum,
      ``sqrtKernel_mul_le, ``graphDecayKernel_mul_le, ``sqrtKernel_graphDecayKernel,
      ``recursiveCommutatorCoeff_step,
      ``exists_orthonormalBasis_uniform_kernel_aux,
      ``exists_orthonormalBasis_uniform_kernel] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

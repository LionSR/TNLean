/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.LowEnergyBasisUniform
import TNLean.Lattice.LowEnergyBasisTruncatedUniform
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Kernel-axiom checks for the constructed bases and actual truncated-term uniform sums. -/

open TNLean.Lattice

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``twoDimensionalSpectralSpread,
      ``eq_smul_one_of_twoDimensionalSpectralSpread_eq_zero,
      ``exists_norm_sub_smul_one_eq_twoDimensionalSpectralSpread,
      ``norm_inner_le_twoDimensionalSpectralSpread,
      ``norm_offDiagonalPartFamily_le_twoDimensionalSpectralSpread,
      ``exists_orthonormalBasis_maximal_twoDimensionalSpectralSpread,
      ``exists_orthonormalBasis_norm_inner_le_sqrt_commutator_decay,
      ``sum_weight_anchor_le_of_support_budget,
      ``sum_weight_mul_exp_neg_edist_le,
      ``exists_twoDimensional_groundSpaceBasis_sum_norm_offDiagonalPartFamily_le,
      ``exists_selfAdjoint_spectral_split,
      ``exists_family_spectral_split,
      ``norm_commutator_compression_le_kernel,
      ``exists_orthonormalBasis_uniform_weighted_kernel,
      ``sum_weight_list_graphDecayKernel_le,
      ``exists_groundSpaceBasis_sum_norm_offDiagonalPartFamily_le_uniform,
      ``commutator_time_window_exp_bounds,
      ``norm_groundCompression_observables_commutator_le_exp,
      ``norm_groundCompression_observables_commutator_le_exp_edist,
      ``exists_groundSpaceBasis_sum_norm_offDiagonalPartFamily_truncated_le] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

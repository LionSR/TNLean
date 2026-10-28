/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.TwoWindowSum
import TNLean.Lattice.DisjointRegionalGround
import TNLean.MPS.AreaLaw.ActualClippedPolynomialFamily
import TNLean.MPS.AreaLaw.FiveRegionHamiltonian
import TNLean.MPS.AreaLaw.FiveRegionTruncationResidual
import TNLean.MPS.AreaLaw.PhysicalDGViability
import TNLean.MPS.AreaLaw.PhysicalIntervalTransport
import TNLean.MPS.AreaLaw.PolynomialFilterParameters
import TNLean.MPS.AreaLaw.RegionalMiddleFactors
import TNLean.MPS.AreaLaw.RegionalTruncationResidual
import TNLean.MPS.AreaLaw.ShortRegionViableFamily
import TNLean.MPS.MPDO.TraceChainOperator
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Foundation checks for the public physical DG family and its supporting results. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[
    ``Matrix.exists_disjoint_regional_clipping_structure,
    ``TNLean.MPS.AreaLaw.internal_bond_support_subset,
    ``TNLean.MPS.AreaLaw.card_internal_bonds_le,
    ``TNLean.MPS.AreaLaw.pairwise_commute_sum_internal_consecutive_regions,
    ``TNLean.MPS.AreaLaw.norm_consecutive_regional_truncation_low_le,
    ``Finset.sum_five_internal_regions_add_crossings,
    ``TNLean.MPS.AreaLaw.five_region_original_bond_data,
    ``Real.five_region_final_clipping_budget_le,
    ``Real.exists_physical_dg_scalar_parameters,
    ``Real.physical_chebyshev_endpoints,
    ``TNLean.MPS.AreaLaw.exists_five_region_dg_cluster_parameters,
    ``Fin.sum_univ_eq_actual_two_window_alphabet,
    ``MPOTensor.exists_traceChainOperator_of_finite_matrix,
    ``TNLean.MPS.AreaLaw.exists_traceChainOperator_of_supported_interval,
    ``FiniteProduct.exists_changingRegional_family_fin,
    ``TNLean.MPS.AreaLaw.exists_actual_regional_clipped_polynomial_family_fin,
    ``TNLean.MPS.AreaLaw.exists_short_actual_region_improving_family,
    ``TNLean.MPS.AreaLaw.inward_effective_cuts,
    ``TNLean.MPS.AreaLaw.collar_card_le_square_at_square_degree,
    ``TNLean.MPS.AreaLaw.exists_physical_dg_viable_family,
    ``TNLean.MPS.AreaLaw.exists_five_region_physical_scaled_low_cluster,
    ``TNLean.MPS.AreaLaw.exists_physical_interval_viable_subspace,
    ``TNLean.MPS.AreaLaw.exists_accuracy_physical_interval_family_and_bootstrap,
    ``Real.exists_dg_accuracy_scalar_parameters,
    ``TNLean.MPS.AreaLaw.collar_card_le_square_of_larger_count_base,
    ``TNLean.MPS.AreaLaw.exists_short_actual_region_improving_family_of_count_base]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

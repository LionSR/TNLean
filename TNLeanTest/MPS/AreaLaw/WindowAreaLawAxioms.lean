/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.MPSApproximation
import TNLean.MPS.AreaLaw.ComponentReduction
import TNLean.MPS.AreaLaw.LogarithmicAreaLaw
import TNLean.MPS.AreaLaw.WindowCounting
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the common budget and
consecutive-window area law and normalized matrix product state approximation. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``TNLean.MPS.AreaLaw.four_le_chainShellCount,
    ``TNLean.MPS.AreaLaw.chainEnergyThreshold_le_chainShellCount,
    ``TNLean.MPS.AreaLaw.chainTailThreshold_le_chainShellCount,
    ``TNLean.MPS.AreaLaw.disjoint_interval_chainBuffer,
    ``TNLean.MPS.AreaLaw.card_chainBuffer_le,
    ``TNLean.MPS.AreaLaw.two_mul_condEntropy_interval_le,
    ``TNLean.MPS.AreaLaw.chainDiscountConst_nonneg,
    ``TNLean.MPS.AreaLaw.chainIntervalEntropyBound_nonneg,
    ``TNLean.MPS.AreaLaw.regionEntropy_interval_le,
    ``TNLean.MPS.AreaLaw.chainShellCount_le,
    ``TNLean.MPS.AreaLaw.chainIntervalEntropyBound_le,
    ``TNLean.MPS.AreaLaw.regionEntropy_le_mul_card_boundaryEdges,
    ``TNLean.MPS.AreaLaw.chainAreaLaw,
    ``TNLean.MPS.AreaLaw.exists_isOpenMPS_norm_sub_le,
    ``TNLean.MPS.AreaLaw.chainBondDimension_le_mul_rpow,
    ``TNLean.MPS.AreaLaw.regionEntropy_le_mul_card_domainBoundaryEdges,
    ``TNLean.MPS.AreaLaw.domainAreaLaw,
    ``TNLean.MPS.AreaLaw.chainAreaLawConst_le_mul_log_cube,
    ``TNLean.MPS.AreaLaw.regionEntropy_le_log_cube_mul_card_boundaryEdges,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.card_crossingTerms_interval_le_of_consecutive_terms,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.log_surprisalMoment_interval_le_of_consecutive_terms,
    ``TNLean.MPS.AreaLaw.card_interval_enlargement_sdiff_le,
    ``TNLean.MPS.AreaLaw.two_mul_condEntropy_interval_le_of_family_budget,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.cutLogBudget_interval_le_of_consecutive_terms,
    ``TNLean.MPS.AreaLaw.chainAreaLaw_of_consecutive_terms,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.regionEntropy_eq_zero_of_range_zero,
    ``TNLean.MPS.AreaLaw.chainAreaLaw_of_consecutive_terms_polynomial_range,
    ``TNLean.MPS.AreaLaw.card_boundaryEdges_prefix_le,
    ``TNLean.MPS.AreaLaw.exists_isOpenMPS_norm_sub_le_of_error_of_consecutive_terms] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

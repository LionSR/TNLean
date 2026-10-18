/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.TwoFamilyAssembly
import Lean.Util.CollectAxioms

/-!
# Logical dependencies of the explicit constant of the two-family decomposition

Each public theorem must exist and use only the three standard logical axioms.
-/

run_cmd do
  let geo := `TNLean.PEPS.AreaLaw.Geometry
  let top := `TNLean.PEPS.AreaLaw
  let names := #[
    geo ++ `polynomialDyadicBudget_pos, geo ++ `sum_le_polynomialDyadicBudget,
    geo ++ `iterateDepthConstant_pos, geo ++ `iterate_depth_le,
    geo ++ `iterateGenerationCountConstant_pos,
    geo ++ `sum_pow_le_iterateGenerationCountConstant,
    geo ++ `repairDescendantCountConstant_pos,
    geo ++ `sum_pow_le_repairDescendantCountConstant,
    geo ++ `repairDescendantLayerConstant_pos,
    geo ++ `sum_pow_le_repairDescendantLayerConstant,
    geo ++ `repairMarkAncestor_prefix_layer_le, geo ++ `initialRepairStage_weighted_sum_le,
    geo ++ `repairMarkCountConstant_pos, geo ++ `repairStage_markIndex_prefix_le,
    geo ++ `initialBeltCountConstant_pos, geo ++ `initial_belt_card_le,
    geo ++ `repairStage_positive_rank_prefix_le, geo ++ `repairRetainedCountConstant_pos,
    geo ++ `repairStage_retained_positive_rank_le, geo ++ `primaryErrorSumConstant_pos,
    geo ++ `primaryPitchIndices_error_sum_le,
    geo ++ `repairStage_retained_positive_rank_error_sum_le,
    geo ++ `one_le_primaryScannerConstant, geo ++ `primaryScannerConstant_spec,
    geo ++ `beltScannerConstant_pos, geo ++ `one_le_repairMarginThreshold,
    geo ++ `repairHalfSide_le_of_repairMarginThreshold_le,
    geo ++ `repairMetricHypotheses_of_le,
    geo ++ `isUniformRepairInduction_of_repairMetricHypotheses,
    geo ++ `isUniformRepairInduction_of_le, geo ++ `descendant_cutClearance_scales_of_le,
    geo ++ `initialBelt_birthTemplate_cutClearance_of_le,
    geo ++ `descendant_birthTemplate_cutClearance_of_le,
    geo ++ `repairStage_birth_templates_of_le, geo ++ `repairStage_primary_error_sum_le,
    geo ++ `exists_isBirthSeparationConstant, geo ++ `IsBirthSeparationConstant.birthSeparated,
    top ++ `isTwoFamilyDecompositionConstant_of_one_le,
    top ++ `IsTwoFamilyDecompositionConstant.ofLe,
    top ++ `isTwoFamilyDecompositionConstant_twoFamilyDecompositionConstant]
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in names do
    unless (← Lean.getEnv).contains decl do
      throwError "The intended declaration is absent: {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (expected.contains ·) do
      throwError "Unexpected logical dependencies for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

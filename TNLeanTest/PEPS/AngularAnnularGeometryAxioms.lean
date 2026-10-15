/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.AngularAnnularCells
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Exact public-declaration kernel dependency guards for the annular geometry -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``TNLean.PEPS.Approximation.exists_annularLayer_cover,
    ``TNLean.PEPS.Approximation.exists_annularLayer_selectedIndices,
    ``TNLean.PEPS.Approximation.exists_annularLayer_square_cover,
    ``TNLean.PEPS.Approximation.exists_annular_newIndices,
    ``TNLean.PEPS.Approximation.annular_selectedRegion_clearance,
    ``TNLean.PEPS.Approximation.dyadicScale,
    ``TNLean.PEPS.Approximation.dyadicScale_zero,
    ``TNLean.PEPS.Approximation.dyadicScale_pos,
    ``TNLean.PEPS.Approximation.dyadicScale_nonneg,
    ``TNLean.PEPS.Approximation.dyadicScale_succ,
    ``TNLean.PEPS.Approximation.two_mul_dyadicScale_succ,
    ``TNLean.PEPS.Approximation.dyadicScale_antitone,
    ``TNLean.PEPS.Approximation.dyadicScale_le,
    ``TNLean.PEPS.Approximation.two_mul_dyadicScale_le,
    ``TNLean.PEPS.Approximation.DyadicCutoff,
    ``TNLean.PEPS.Approximation.exists_dyadicCutoff,
    ``TNLean.PEPS.Approximation.chooseDyadicCutoff,
    ``TNLean.PEPS.Approximation.DyadicCutoff.lower_at,
    ``TNLean.PEPS.Approximation.cappedMarkDistance,
    ``TNLean.PEPS.Approximation.cappedMarkDistance_empty,
    ``TNLean.PEPS.Approximation.cappedMarkDistance_eq_min_of_nonempty,
    ``TNLean.PEPS.Approximation.le_cappedMarkDistance_iff,
    ``TNLean.PEPS.Approximation.cappedMarkDistance_le_cap,
    ``TNLean.PEPS.Approximation.cappedMarkDistance_le_dist,
    ``TNLean.PEPS.Approximation.cappedMarkDistance_nonneg,
    ``TNLean.PEPS.Approximation.cappedMarkDistance_lt_iff,
    ``TNLean.PEPS.Approximation.annularLayer,
    ``TNLean.PEPS.Approximation.annularLayer_sole,
    ``TNLean.PEPS.Approximation.annularLayer_first,
    ``TNLean.PEPS.Approximation.annularLayer_middle,
    ``TNLean.PEPS.Approximation.annularLayer_last,
    ``TNLean.PEPS.Approximation.mem_annularLayer_middle_iff,
    ``TNLean.PEPS.Approximation.mem_annularLayer_last_iff,
    ``TNLean.PEPS.Approximation.annularLayer_subset,
    ``TNLean.PEPS.Approximation.cumulativeLayer,
    ``TNLean.PEPS.Approximation.cumulativeLayer_zero,
    ``TNLean.PEPS.Approximation.cumulativeLayer_subset,
    ``TNLean.PEPS.Approximation.annularLayer_subset_cumulativeLayer,
    ``TNLean.PEPS.Approximation.cumulativeLayer_mono,
    ``TNLean.PEPS.Approximation.cumulativeLayer_succ,
    ``TNLean.PEPS.Approximation.mem_cumulativeLayer_iff,
    ``TNLean.PEPS.Approximation.cumulativeLayer_last,
    ``TNLean.PEPS.Approximation.exists_mem_annularLayer,
    ``TNLean.PEPS.Approximation.annularLayer_disjoint,
    ``TNLean.PEPS.Approximation.cumulativeLayer_disjoint_next,
    ``TNLean.PEPS.Approximation.exists_mark_near_of_mem_annularLayer,
    ``TNLean.PEPS.Approximation.annularLayer_empty_marks_zero,
    ``TNLean.PEPS.Approximation.annularLayer_empty_marks_of_pos,
    ``TNLean.PEPS.Approximation.AngularSeparation,
    ``TNLean.PEPS.Approximation.cumulativeLayer_separation_nonfinal,
    ``TNLean.PEPS.Approximation.cumulativeLayer_separation,
    ``TNLean.PEPS.Approximation.AngularGrid.selectedRegion,
    ``TNLean.PEPS.Approximation.AngularGrid.near_union,
    ``TNLean.PEPS.Approximation.AngularGrid.near_mono,
    ``TNLean.PEPS.Approximation.AngularGrid.near_subset_selectedRegion,
    ``TNLean.PEPS.Approximation.AngularGrid.selectedRegion_subset_near,
    ``TNLean.PEPS.Approximation.AngularGrid.selectedRegion_mono,
    ``TNLean.PEPS.Approximation.AngularGrid.touches_new_of_not_old,
    ``TNLean.PEPS.Approximation.AngularGrid.exists_newIndices_scaled,
    ``TNLean.PEPS.Approximation.AngularGrid.selectedRegion_clearance,
    ``TNLean.PEPS.Approximation.AngularGrid.near_core_clearance,
    ``TNLean.PEPS.Approximation.AngularGrid.old_selectedRegion_subset,
    ``TNLean.PEPS.Approximation.AngularGrid.exterior_near_subset,
    ``TNLean.PEPS.Approximation.AngularGrid.angular_core_subsets,
    ``TNLean.PEPS.Approximation.AngularGrid.angular_clearance_pos,
    ``TNLean.PEPS.Approximation.AngularGrid.angular_selectedRegion_clearance,
    ``TNLean.PEPS.Approximation.AngularGrid.angular_physical_disjoint,
    ``TNLean.PEPS.Approximation.AngularGrid.angular_target_core_clearance,
    ``TNLean.PEPS.Approximation.AngularGrid.angular_exterior_core_clearance,
    ``TNLean.PEPS.Approximation.AngularGrid.exists_angular_cell_reset_width,
    ``TNLean.PEPS.Approximation.AngularGrid.cell,
    ``TNLean.PEPS.Approximation.AngularGrid.owner,
    ``TNLean.PEPS.Approximation.AngularGrid.near,
    ``TNLean.PEPS.Approximation.AngularGrid.touches,
    ``TNLean.PEPS.Approximation.AngularGrid.mem_cell_owner,
    ``TNLean.PEPS.Approximation.AngularGrid.owner_eq_of_mem_cell,
    ``TNLean.PEPS.Approximation.AngularGrid.cell_index_unique,
    ``TNLean.PEPS.Approximation.AngularGrid.dist_le_of_mem_cell,
    ``TNLean.PEPS.Approximation.AngularGrid.indexBox,
    ``TNLean.PEPS.Approximation.AngularGrid.card_indexBox,
    ``TNLean.PEPS.Approximation.AngularGrid.mem_indexBox_of_dist_le,
    ``TNLean.PEPS.Approximation.AngularGrid.candidateIndices,
    ``TNLean.PEPS.Approximation.AngularGrid.card_candidateIndices_le,
    ``TNLean.PEPS.Approximation.AngularGrid.touches_mem_candidateIndices,
    ``TNLean.PEPS.Approximation.AngularGrid.exists_selectedIndices_of_cover,
    ``TNLean.PEPS.Approximation.AngularGrid.touches_mem_candidateIndices_scaled,
    ``TNLean.PEPS.Approximation.AngularGrid.exists_selectedIndices_scaled]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.HierarchyRadius
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Foundation checks for the explicit hierarchy radii and gap-dependent projection length. -/

open TNLean.MPS.AreaLaw.LocalSolution

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``monotone_hierarchyMajorant, ``hierarchyWindowRadius_pos,
      ``hierarchyMajorant_exp_le, ``hierarchyDeficiency_window_lt_one,
      ``hierarchyWindowRadius_le, ``eighth_le_one_sub_inv_pow_succ,
      ``hierarchyDeficiency_window_succ_le, ``hierarchyDeficiency_window_succ_lt_one,
      ``hierarchyProjectionLength, ``hierarchyWindowEnergy_le_quarter_gap,
      ``hierarchyProjectionLength_ge_square, ``closing_threshold_lt_hierarchyProjectionLength,
      ``hierarchyDeficiency_window_succ_lt_one_of_length,
      ``hierarchyWindowRadius_le_quarter_gap_div, ``hierarchySum_le_const,
      ``hierarchySum_windowRadius_add_le, ``hierarchySum_windowRadius_add_le_quarter_gap,
      ``hierarchyTruncationError_le_eighth_gap] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

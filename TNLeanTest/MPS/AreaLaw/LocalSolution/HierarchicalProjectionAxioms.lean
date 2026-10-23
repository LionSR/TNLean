/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.HierarchicalProjection
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for one level of Hastings' hierarchical projection and
the recursion of its deficiencies. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``TNLean.MPS.AreaLaw.LocalSolution.re_inner_toEuclideanLin_eq_norm_sq,
    ``TNLean.MPS.AreaLaw.LocalSolution.norm_sq_add_norm_sub_sq,
    ``TNLean.MPS.AreaLaw.LocalSolution.re_inner_eq_one_sub_norm_sub_sq,
    ``TNLean.MPS.AreaLaw.LocalSolution.one_sub_le_re_inner_of_norm_sub_le,
    ``TNLean.MPS.AreaLaw.LocalSolution.one_sub_sq_le_re_inner_of_norm_sub_le,
    ``TNLean.MPS.AreaLaw.LocalSolution.norm_sub_mul_sq_le_of_isStarProjection,
    ``TNLean.MPS.AreaLaw.LocalSolution.norm_inv_norm_smul_sub_le,
    ``TNLean.MPS.AreaLaw.LocalSolution.norm_inv_norm_smul_toEuclideanLin_sub_sq_le,
    ``TNLean.MPS.AreaLaw.LocalSolution.norm_inv_norm_smul_sub_le_two_mul,
    ``TNLean.MPS.AreaLaw.LocalSolution.norm_sub_sq_le_of_mul_eq,
    ``TNLean.MPS.AreaLaw.LocalSolution.ofReal_smul_one_eq_algebraMap,
    ``TNLean.MPS.AreaLaw.LocalSolution.isHermitian_sub_ofReal_smul_one,
    ``TNLean.MPS.AreaLaw.LocalSolution.windowProjection,
    ``TNLean.MPS.AreaLaw.LocalSolution.isStarProjection_windowProjection,
    ``TNLean.MPS.AreaLaw.LocalSolution.compressedWindowProjection,
    ``TNLean.MPS.AreaLaw.LocalSolution.commute_windowProjection_compress,
    ``TNLean.MPS.AreaLaw.LocalSolution.isStarProjection_compressedWindowProjection,
    ``TNLean.MPS.AreaLaw.LocalSolution.compressedWindowProjection_mul,
    ``TNLean.MPS.AreaLaw.LocalSolution.toEuclideanLin_compressedWindowProjection_of_mem,
    ``TNLean.MPS.AreaLaw.LocalSolution.toEuclideanLin_compressedWindowProjection_eq_zero,
    ``TNLean.MPS.AreaLaw.LocalSolution.norm_sub_compressedWindowProjection_le,
    ``TNLean.MPS.AreaLaw.LocalSolution.norm_sub_compressedWindowProjection_le_of_norm_sub_le,
    ``TNLean.MPS.AreaLaw.LocalSolution.norm_sub_windowProjection_le,
    ``TNLean.MPS.AreaLaw.LocalSolution.one_sub_div_le_re_inner_windowProjection,
    ``TNLean.MPS.AreaLaw.LocalSolution.one_sub_div_sq_le_re_inner_windowProjection,
    ``TNLean.MPS.AreaLaw.LocalSolution.windowProjection_eq_zero,
    ``TNLean.MPS.AreaLaw.LocalSolution.exists_mem_spectrum_abs_sub_le,
    ``TNLean.MPS.AreaLaw.LocalSolution.norm_toEuclideanLin_le_add,
    ``TNLean.MPS.AreaLaw.LocalSolution.norm_sub_ofReal_smul_one_le,
    ``TNLean.MPS.AreaLaw.LocalSolution.norm_sub_smul_one_le_two_mul,
    ``TNLean.MPS.AreaLaw.LocalSolution.abs_re_inner_toEuclideanLin_le,
    ``TNLean.MPS.AreaLaw.LocalSolution.norm_sub_windowProjection_le_of_norm_sub_le,
    ``TNLean.MPS.AreaLaw.LocalSolution.norm_toEuclideanLin_compress_sub_le,
    ``TNLean.MPS.AreaLaw.LocalSolution.levelDeficiency,
    ``TNLean.MPS.AreaLaw.LocalSolution.levelDeficiency_zero,
    ``TNLean.MPS.AreaLaw.LocalSolution.levelDeficiency_succ,
    ``TNLean.MPS.AreaLaw.LocalSolution.levelDeficiency_nonneg,
    ``TNLean.MPS.AreaLaw.LocalSolution.levelDeficiency_le,
    ``TNLean.MPS.AreaLaw.LocalSolution.levelDeficiency_two_le,
    ``TNLean.MPS.AreaLaw.LocalSolution.one_sub_inv_natCast_mem_Icc,
    ``TNLean.MPS.AreaLaw.LocalSolution.quarter_le_one_sub_inv_pow,
    ``TNLean.MPS.AreaLaw.LocalSolution.levelDeficiency_self_le,
    ``TNLean.MPS.AreaLaw.LocalSolution.levelDeficiency_exp_le,
    ``TNLean.MPS.AreaLaw.LocalSolution.levelDeficiency_le_rpow_quarter] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

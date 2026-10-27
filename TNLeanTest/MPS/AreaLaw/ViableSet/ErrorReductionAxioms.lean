/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.ErrorReduction
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
The public error-reduction results are present and depend only on the three standard axioms.
-/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``TNLean.MPS.AreaLaw.cutMatrix_toEuclideanLin,
    ``TNLean.MPS.AreaLaw.cutMatrix_toEuclideanLin_eq_sum,
    ``TNLean.MPS.AreaLaw.errorReductionSet,
    ``TNLean.MPS.AreaLaw.toEuclideanLin_mem_errorReductionSet,
    ``TNLean.MPS.AreaLaw.card_errorReductionSet_le,
    ``TNLean.MPS.AreaLaw.toEuclideanLin_mem_span_errorReductionSet,
    ``TNLean.MPS.AreaLaw.toEuclideanLin_mem_leftSupportSubmodule_errorReductionSet,
    ``TNLean.MPS.AreaLaw.mul_norm_le_norm_inner_of_norm_sub_le,
    ``TNLean.MPS.AreaLaw.isViable_errorReductionSet_of_witness,
    ``TNLean.MPS.AreaLaw.norm_inner_le_norm_toEuclideanLin_of_fixed,
    ``TNLean.MPS.AreaLaw.IsViable.errorReduction,
    ``TNLean.MPS.AreaLaw.IsViableMPS.errorReduction] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

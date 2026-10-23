/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.SchmidtDiagonalChain
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the chain stage form of Hastings' Lemma 3 on
correlations of Schmidt-diagonal operators. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``TNLean.MPS.AreaLaw.Hastings.l2_opNorm_schmidtDiagonal_le_one,
    ``TNLean.MPS.AreaLaw.Hastings.commute_reindex_one_kronecker_of_isSupportedOn,
    ``TNLean.MPS.AreaLaw.Hastings.toEuclideanCLM_reindex_cutEquiv_symm,
    ``TNLean.MPS.AreaLaw.Hastings.norm_inner_mul_sub_le_of_factorization] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

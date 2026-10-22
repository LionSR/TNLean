/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.SchmidtDiagonalCorrelation
import TNLean.MPS.AreaLaw.Hastings.SchmidtDiagonalOperators
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the operator estimate of Hastings' Lemma 3 on
correlations of Schmidt-diagonal operators. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``Matrix.norm_toEuclideanCLM_sub_self_le_of_posSemidef,
    ``TNLean.MPS.AreaLaw.Hastings.norm_inner_sub_le_of_projector_factorization,
    ``TNLean.MPS.AreaLaw.Hastings.kronecker_one_mulVec_schmidt_eq_one_kronecker_mulVec] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

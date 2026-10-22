/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.PositiveFactorization
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the positive version of Hastings' approximate
factorization. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``Entropy.IsSupportedOn.conjTranspose,
    ``TNLean.MPS.AreaLaw.Hastings.isStarProjection_vecMulVec_of_norm_eq_one,
    ``TNLean.MPS.AreaLaw.Hastings.sqrt_one_sub_sq_add_le,
    ``TNLean.MPS.AreaLaw.Hastings.IsFactorizationAt.conjTranspose_mul_self,
    ``TNLean.MPS.AreaLaw.Hastings.exists_posSemidef_factorization,
    ``TNLean.MPS.AreaLaw.Hastings.exists_factorization_of_isFactorizationAt] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

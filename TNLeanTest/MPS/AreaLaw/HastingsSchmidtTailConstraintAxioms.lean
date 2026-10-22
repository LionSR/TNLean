/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.SchmidtTailConstraint
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for Hastings' Schmidt-tail constraint on the chain. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``TNLean.MPS.AreaLaw.Hastings.one_sub_kyFanNorm_le_of_schmidtRank_mixture,
    ``TNLean.MPS.AreaLaw.Hastings.exists_mixture_rank_cutMatrix_le_overlap_of_factorization,
    ``TNLean.MPS.AreaLaw.Hastings.one_sub_kyFanNorm_le_of_factorization,
    ``TNLean.MPS.AreaLaw.Hastings.one_half_le_kyFanNorm_of_exp_two_mul_vonNeumannEntropy_le,
    ``TNLean.MPS.AreaLaw.Hastings.one_sub_kyFanNorm_le_of_factorization_of_entropy] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

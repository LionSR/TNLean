/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.ChainBootstrap
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the chain form of Hastings' bootstrap lemma. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``TNLean.MPS.AreaLaw.Hastings.star_cutVector_dotProduct,
    ``TNLean.MPS.AreaLaw.Hastings.regionEntropy_interval_eq,
    ``TNLean.MPS.AreaLaw.Hastings.rank_cutMatrix_le_pow_of_lt,
    ``TNLean.MPS.AreaLaw.Hastings.entropy_le_of_overlap_schmidtRank_mixture_of_factorization] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.SchmidtRankRenyiBootstrap
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the Rényi stage of Hastings' bootstrap lemma and
the Schmidt-tail lemma it shares with the von Neumann stage. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``TNLean.MPS.AreaLaw.Hastings.eigenvalues₀_nonneg_and_sum_eq_one,
    ``TNLean.MPS.AreaLaw.Hastings.exists_eigenvalues₀_tail_le_of_schmidtRank_mixtures,
    ``TNLean.MPS.AreaLaw.Hastings.vonNeumannEntropy_le_of_schmidtRank_mixtures,
    ``TNLean.MPS.AreaLaw.Hastings.renyiEntropy_eq_log_sum_eigenvalues₀_rpow,
    ``TNLean.MPS.AreaLaw.Hastings.renyiEntropy_le_of_schmidtRank_mixtures] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

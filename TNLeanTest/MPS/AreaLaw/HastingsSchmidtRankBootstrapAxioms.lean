/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.SchmidtRankBootstrap
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the stage form of Hastings' bootstrap lemma. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``TNLean.MPS.AreaLaw.Hastings.normSq_dotProduct_le_kyFanNorm,
    ``vonNeumannEntropy_eq_probabilityEntropy_eigenvalues₀,
    ``Matrix.IsHermitian.sum_eigenvalues₀_filter_le,
    ``TNLean.MPS.AreaLaw.Hastings.vonNeumannEntropy_le_of_schmidtRank_mixtures] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.CoarseInformationFromGap
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Permitted axioms for coarse mutual information from the original spectral gap. -/

run_cmd do
  let decls := #[
    ``TNLean.PEPS.Approximation.coarse_mutualInformation_le,
    ``TNLean.PEPS.Approximation.coarse_mutualInformation_le_square,
    ``TNLean.PEPS.Approximation.coarse_mutualInformation_le_translated_square]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

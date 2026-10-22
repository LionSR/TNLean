/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.MainTheorem
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Logical dependencies of the contradiction argument of Hastings' area-law proof. -/

open TNLean.MPS.AreaLaw.Hastings

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``maxEntropyBound_nonneg, ``maxEntropyBound_le, ``maxEntropyBound_le_of_one_le,
      ``compl_interval_zero,
      ``regionEntropy_interval_zero_le, ``regionEntropy_prefix_le_of_windowClaim] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

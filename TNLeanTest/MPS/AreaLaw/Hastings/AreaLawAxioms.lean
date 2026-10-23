/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.AreaLaw
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Logical dependencies of Hastings' area law on the chain from Lemma 1. -/

open TNLean.MPS.AreaLaw.Hastings

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``areaLawBound_le, ``regionEntropy_prefix_le_of_factorization,
      ``regionEntropy_prefix_le_of_windowClaim_of_le] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

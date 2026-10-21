/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.AreaLaw.WindowCounting
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Logical dependencies of the consecutive-window count and physical moment estimate. -/

open TNLean.MPS.AreaLaw

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``ChainHamiltonian.card_crossingTerms_interval_le_of_consecutive_terms,
      ``ChainHamiltonian.log_surprisalMoment_interval_le_of_consecutive_terms] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

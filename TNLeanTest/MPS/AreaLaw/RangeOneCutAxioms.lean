/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.RangeOneCut
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Permitted-axiom checks for the normalized range-one cut decomposition. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.MPS.AreaLaw.IsChainSupport.eq_interval_of_splits_of_range_one,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.exists_cut_decomposition_of_range_one] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

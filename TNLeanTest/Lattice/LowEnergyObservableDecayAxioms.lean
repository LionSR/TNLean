/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.LowEnergyObservableDecay
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Kernel-axiom checks for the decay estimate on a separate local-observable family. -/

open TNLean.Lattice

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``commutator_time_window_exp_bounds, ``le_anchorDecay_of_separated_exp,
      ``norm_groundCompression_observables_commutator_le_exp,
      ``norm_groundCompression_observables_commutator_le_exp_edist] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

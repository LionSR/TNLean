/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.GaussianFilteredTruncation
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for Hastings' truncated approximation of a
Gaussian-filtered term. -/

open TNLean.Lattice

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``norm_conj_sub_conj_le,
      ``norm_gaussianFilteredTerm_sub_le,
      ``hermitianUnitaryPath_conj_mem_supportedOperators,
      ``gaussianFilteredTerm_mem_supportedOperators,
      ``norm_commutator_heisenbergEvolution_le_graphDistance_finset,
      ``norm_commutator_sub_truncated_le,
      ``norm_gaussianFilteredTerm_sub_truncated_le_sum,
      ``norm_gaussianFilteredTerm_sub_truncated_le,
      ``exists_truncated_approx_gaussianFilteredTerm] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

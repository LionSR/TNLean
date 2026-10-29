/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.TranslationFiniteOrbitCommutator
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Kernel-axiom checks for general translation-invariant low-energy commutators. -/

open TNLean.Lattice

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``norm_groundCompression_commutator_le_of_finite_observable_orbit,
      ``norm_groundCompression_commutator_le_finite_translation_exp,
      ``norm_groundCompression_truncated_commutator_le_finite_translation_exp] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

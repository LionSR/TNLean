/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.TranslationSupercellCommutator
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the low-energy commutators of a translation-invariant
lattice. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
      ``Matrix.norm_sitePermMatrix_mul_mul_conjTranspose,
      ``TNLean.Lattice.norm_groundCompression_commutator_le_of_momenta,
      ``TNLean.Lattice.norm_groundCompression_commutator_le_of_momenta_exp,
      ``TNLean.Lattice.norm_groundCompression_commutator_le_of_norm_sub_le,
      ``TNLean.Lattice.norm_groundCompression_commutator_truncated_le_of_momenta] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

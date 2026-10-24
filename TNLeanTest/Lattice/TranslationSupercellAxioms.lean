/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.TranslationSupercell
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the supercell step of Hastings' translation-invariant
case: low-energy compressions are unchanged by translations that fix every ground vector. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
      ``Submodule.starProjection_mul_conj_mul_starProjection,
      ``Matrix.sitePermMatrix_inv,
      ``TNLean.Lattice.starProjection_mul_sitePermMatrix_conj_mul_starProjection,
      ``TNLean.Lattice.groundCompression_commutator_eq_of_mem_supercell,
      ``TNLean.Lattice.norm_groundCompression_commutator_le_of_mem_supercell] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

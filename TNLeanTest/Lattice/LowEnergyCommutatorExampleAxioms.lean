/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.LowEnergyCommutatorExample
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the example of Hastings' Appendix B in which the
compressions of local terms to a degenerate ground space fail to commute. -/

open TNLean.Lattice.LowEnergyExample in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
      ``hamiltonian_eq_diagonal,
      ``groundEnergy_le,
      ``energy_eq_groundEnergy_iff,
      ``hamiltonian_mulVec_eq_iff,
      ``not_commute_compress_term_zero_one,
      ``not_commute_compress_term_one_two,
      ``not_commute_compress_term_zero_two,
      ``commute_compress_term_zero_of_three_le] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

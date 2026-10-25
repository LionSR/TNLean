/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.LowEnergyCommutatorSum
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the sum of the low-energy commutators over all
terms. -/

open TNLean.Lattice

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``add_one_pow_mul_exp_neg_le, ``sum_add_one_pow_mul_exp_neg_le,
      ``sum_exp_neg_edist_le, ``norm_groundCompression_le,
      ``norm_groundCompression_commutator_le_two_mul, ``isSelfAdjoint_groundCompression,
      ``norm_groundCompression_commutator_le_exp, ``disjoint_biUnion_graphBall_of_lt_edist,
      ``norm_groundCompression_commutator_le_exp_edist,
      ``sum_norm_groundCompression_commutator_le, ``sum_norm_offDiagonalPartFamily_le_oibu] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

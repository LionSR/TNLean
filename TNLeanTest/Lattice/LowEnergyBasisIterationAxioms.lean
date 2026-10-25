/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.LowEnergyBasisIteration
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for a basis of a degenerate ground space by iterated
compressions. -/

open TNLean.Lattice

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``inner_commutator_apply_eq_sum, ``abs_sub_mul_norm_inner_le, ``labelClass,
      ``levelGap, ``levelGap_pos, ``levelGap_le, ``norm_inner_le_of_mem_labelClass,
      ``norm_inner_le_of_two_levels, ``norm_offDiagonalPartFamily_le_of_two_levels] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.LowEnergyBasis
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the basis of a two-dimensional ground space. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``TNLean.Lattice.offDiagonalPart,
    ``TNLean.Lattice.offDiagonalPart_apply,
    ``TNLean.Lattice.norm_offDiagonalPart_le,
    ``TNLean.Lattice.norm_offDiagonalPart_le_norm_commutator_div,
    ``TNLean.Lattice.sum_norm_offDiagonalPart_le,
    ``TNLean.Lattice.norm_apply_sub_inner_smul_le_add_offDiagonalPart] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

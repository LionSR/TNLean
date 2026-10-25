/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.LowEnergyBasisSimpleSpectrum
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for a ground-space basis diagonalizing one compression
with simple spectrum. -/

open TNLean.Lattice

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``shiftPart_apply, ``norm_shiftPart_le, ``norm_offDiagonalPartFamily_le,
      ``norm_offDiagonalPartFamily_le_norm_commutator_div, ``sum_norm_offDiagonalPartFamily_le,
      ``offDiagonalPartFamily_apply_self,
      ``norm_apply_sub_inner_smul_le_add_offDiagonalPartFamily] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

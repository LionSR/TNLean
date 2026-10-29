/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.LowEnergyBasisPerturbation
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Kernel-axiom checks for transferring the basis bound through a growing truncation radius. -/

open TNLean.Lattice

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``offDiagonalPartFamily_sub, ``norm_offDiagonalPartFamily_le_mul_norm,
      ``norm_offDiagonalPartFamily_le_add, ``norm_groundCompression_sub_le,
      ``sum_norm_offDiagonalPartFamily_groundCompression_le,
      ``exists_groundSpaceBasis_sum_norm_offDiagonalPartFamily_truncated_perturbation_le] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.GaussianGroundStateOverlap
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Permitted-axiom checks for the ground state of the actual truncated Hamiltonian -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.Lattice.groundEigenspace_gap_le_of_eigenvalues,
      ``TNLean.Lattice.exists_groundVector_energy_le_of_norm_sub_le,
      ``TNLean.Lattice.exists_groundVector_overlap_of_norm_sub_le,
      ``TNLean.Lattice.exists_groundVector_projected_mass_of_norm_sub_le,
      ``TNLean.Lattice.exp_error_le_of_log_radius,
      ``TNLean.Lattice.exists_groundVector_overlap_of_exp_norm_bound,
      ``TNLean.Lattice.exists_groundVector_projection_of_exp_norm_bound,
      ``TNLean.Lattice.exists_metric_truncated_groundVector_projection,
      ``TNLean.Lattice.exists_metric_truncated_groundVector_overlap] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

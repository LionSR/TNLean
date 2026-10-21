/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/

import TNLean.PEPS.Approximation.SwappedLocalHamiltonian
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# The partially swapped Hamiltonian at range `R`: axiom checks

The imported declarations use only propositional extensionality, classical
choice, and quotient soundness.
-/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[
    ``TNLean.Lattice.card_admissibleSupport_le,
    ``TNLean.Lattice.exists_walks_of_mem_crossingSites,
    ``TNLean.Lattice.LocalHamiltonian.swappedDoubled_operator,
    ``TNLean.Lattice.LocalHamiltonian.swapped_doubled_boundary_bound,
    ``TNLean.Lattice.LocalHamiltonian.supported_buffer_gaussian_integral]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

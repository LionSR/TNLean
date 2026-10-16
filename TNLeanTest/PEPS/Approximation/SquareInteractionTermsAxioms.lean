/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SquareInteractionTerms
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Axiom audit for the nearest-neighbor decomposition of the original square Hamiltonian. -/

run_cmd do
  let decl := ``TNLean.PEPS.Approximation.SquareHamiltonian.exists_nearestNeighbor_terms
  unless (← Lean.getEnv).contains decl do
    throwError "Missing declaration {decl}"
  let axioms ← Lean.collectAxioms decl
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"

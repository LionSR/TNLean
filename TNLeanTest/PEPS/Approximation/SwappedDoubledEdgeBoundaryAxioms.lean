/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/

import TNLean.PEPS.Approximation.SwappedDoubledEdgeBoundary
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Axiom check for the edge-boundary estimate

The estimate uses only propositional extensionality, classical choice,
and quotient soundness.
-/

run_cmd do
  let decl := ``TNLean.Lattice.LocalHamiltonian.swapped_doubled_boundary_bound_edgeBoundary
  unless (← Lean.getEnv).contains decl do
    throwError "Missing declaration {decl}"
  let axioms ← Lean.collectAxioms decl
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"

open Matrix QuantumCircuit
open scoped BigOperators Kronecker Matrix.Norms.L2Operator

-- Empty cuts have zero perturbation, including at local dimension zero.

example {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J : ℝ}
    (h : TNLean.Lattice.LocalHamiltonian Λ q R J) (hJ : 0 ≤ J) :
    let p := sitePairConfigurationEquiv (TNLean.Lattice.Site Λ) q q
    let K := Matrix.reindex p p (doubledHamiltonian h.operator)
    let F := Matrix.reindex p p
      (TNLean.Lattice.sheetSwapOp q (∅ : Finset (TNLean.Lattice.Site Λ)))
    ‖F * K * Fᴴ - K‖ = 0 := by
  intro p K F
  apply le_antisymm ?_ (norm_nonneg _)
  simpa [TNLean.Lattice.edgeBoundary, F, K, p] using
    h.swapped_doubled_boundary_bound_edgeBoundary hJ (∅ : Finset (TNLean.Lattice.Site Λ))

-- Full cut, with arbitrary local dimension and finite domain.
example {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J : ℝ}
    (h : TNLean.Lattice.LocalHamiltonian Λ q R J) (hJ : 0 ≤ J) :
    let p := sitePairConfigurationEquiv (TNLean.Lattice.Site Λ) q q
    let K := Matrix.reindex p p (doubledHamiltonian h.operator)
    let F := Matrix.reindex p p
      (TNLean.Lattice.sheetSwapOp q (Finset.univ : Finset (TNLean.Lattice.Site Λ)))
    ‖F * K * Fᴴ - K‖ = 0 := by
  intro p K F
  apply le_antisymm ?_ (norm_nonneg _)
  simpa [TNLean.Lattice.edgeBoundary, F, K, p] using
    h.swapped_doubled_boundary_bound_edgeBoundary hJ
      (Finset.univ : Finset (TNLean.Lattice.Site Λ))

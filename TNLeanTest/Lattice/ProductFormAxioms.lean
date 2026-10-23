/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ProductForm
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the matrix product form of Trotter products in
Hastings' treatment of nonzero temperature. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``QuantumCircuit.apply_eq_apply_of_mem_supportedOperators,
    ``QuantumCircuit.exp_mem_supportedOperators,
    ``TNLean.Lattice.hasProductForm_one,
    ``TNLean.Lattice.HasProductForm.mul,
    ``TNLean.Lattice.hasProductForm_list_prod,
    ``TNLean.Lattice.HasProductForm.pow,
    ``TNLean.Lattice.hasProductForm_of_mem_supportedOperators,
    ``TNLean.Lattice.LocalHamiltonian.hasProductForm_trotterProduct] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

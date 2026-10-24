/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.SiteSymmetry
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the site permutations of a finite system. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Matrix.sitePermMatrix_mul, ``Matrix.sitePermMatrix_mem_unitaryGroup,
    ``Matrix.sitePermMatrix_mul_mul_conjTranspose,
    ``Matrix.sitePermMatrix_mul_mul_conjTranspose_mem_supportedOperators,
    ``Matrix.isSiteInvariant_of_conj, ``Matrix.isSiteInvariant_sum_of_covariant,
    ``Matrix.isSiteInvariant_sum_conj, ``Matrix.gaussianFilteredTerm_conj,
    ``Matrix.gaussianFilteredTerm_sitePermMatrix_conj, ``Matrix.edist_smul_of_adj_iff,
    ``Matrix.cycleGraph_adj_smul,
    ``QuantumCircuit.supportedOperators_submatrix_siteEquiv] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

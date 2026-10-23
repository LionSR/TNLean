/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.VariationalLowerBound
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the variational lower bound on the ground energy. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Matrix.conjTranspose_commutatorIter, ``Matrix.isHermitian_smul_commutatorIter,
    ``Matrix.commutatorIter_sum, ``Matrix.commutatorIter_self_succ, ``Matrix.commutatorIter_conj,
    ``Matrix.posSemidef_sub_card_smul_of_conj, ``Matrix.card_mul_le_of_mulVec_eq_smul_of_conj,
    ``Matrix.sitePermMatrix_mul, ``Matrix.sitePermMatrix_mem_unitaryGroup,
    ``Matrix.commute_sitePermMatrix_sum,
    ``Matrix.card_mul_le_of_mulVec_eq_smul_of_sitePerm] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

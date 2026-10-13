/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PointwiseChoiceCoefficient
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom checks for mixed coefficients and their gate-label expansion -/

set_option linter.hashCommand false

run_cmd do
  let decls := #[
    ``TNLean.PEPS.PairEffect.SourceCircuit.coefficient_all_mul_conj_eq_prod_nonemptyGateLocations,
    ``TNLean.PEPS.PairEffect.SourceCircuit.sum_coefficient_all_mul_conj_smul_eq_sum_nonemptyGateLabels]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in decls do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

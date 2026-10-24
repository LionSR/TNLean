/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.FinalStateCount
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the count of low-energy orthonormal states. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.MPS.AreaLaw.LocalSolution.inner_toEuclideanCLM_eq_inner_self,
    ``TNLean.MPS.AreaLaw.LocalSolution.re_inner_toEuclideanCLM_eq_norm_sq,
    ``TNLean.MPS.AreaLaw.LocalSolution.sum_norm_sq_le_re_trace,
    ``TNLean.MPS.AreaLaw.LocalSolution.one_sub_mul_card_le_re_trace,
    ``TNLean.MPS.AreaLaw.LocalSolution.card_le_two_mul_re_trace] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

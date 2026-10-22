/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.ProductStateExpectation
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the expectation bounds that follow from the
approximate factorization of the ground-state projector in Hastings' area-law proof. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``TNLean.MPS.AreaLaw.Hastings.norm_toEuclideanCLM_one_sub_le,
    ``TNLean.MPS.AreaLaw.Hastings.sq_one_sub_two_mul_le_re_inner_conjTranspose_mul,
    ``TNLean.MPS.AreaLaw.Hastings.one_sub_sq_le_re_inner_left,
    ``TNLean.MPS.AreaLaw.Hastings.one_sub_sq_le_re_inner_right,
    ``TNLean.MPS.AreaLaw.Hastings.one_sub_two_mul_sq_le_re_trace_kronecker_marginals_mul] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.CutProductExpectation
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for expectations in the product of the two marginals
across a cut. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``TNLean.MPS.AreaLaw.Hastings.trace_cutPureState_mul_cutOperator,
    ``TNLean.MPS.AreaLaw.Hastings.trace_cutProductState_mul_mul,
    ``TNLean.MPS.AreaLaw.Hastings.trace_cutProductState_mul_of_isSupportedOn_left,
    ``TNLean.MPS.AreaLaw.Hastings.trace_cutProductState_mul_of_isSupportedOn_right] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

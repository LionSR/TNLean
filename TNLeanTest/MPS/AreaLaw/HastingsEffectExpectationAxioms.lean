/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.EffectExpectation
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the bound on the expectation of `O_B` in the product
of the marginals, eq. `xbd` of Hastings' area-law proof by route 1 of the note added. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``Matrix.PosSemidef.norm_trace_mul_mul_le,
    ``Matrix.PosSemidef.re_trace_mul_mul_self_le,
    ``TNLean.MPS.AreaLaw.Hastings.re_trace_mul_le_of_projection_sandwich] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.IntervalMutualInformation
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the bound on the mutual information of two
adjacent intervals by one effect, eq. `LU` of Hastings' area-law proof on the chain. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``TNLean.MPS.AreaLaw.Hastings.partialTraceLeft_regionState_union,
    ``TNLean.MPS.AreaLaw.Hastings.trace_cutProductState_mul_localLift_union,
    ``TNLean.MPS.AreaLaw.Hastings.binaryRelativeEntropy_le_intervalMutualInformation] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

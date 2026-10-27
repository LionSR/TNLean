/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.TraceIntervalTransfer
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Exact declaration dependencies for TraceIntervalTransfer -/

run_cmd do
  let env ← Lean.getEnv
  let expectations : Array (Lean.Name × Array Lean.Name) := #[
    (``TNLean.MPS.AreaLaw.exists_traceChainOperator_changingRegionalMiddleFactor,
      #[``propext, ``Classical.choice, ``Quot.sound]),
    (``TNLean.MPS.AreaLaw.changingRegionalMiddleFamily_trace_and_global_decomposition,
      #[``propext, ``Classical.choice, ``Quot.sound])]
  for (decl, expected) in expectations do
    unless env.contains decl do
      throwError "Missing public declaration {decl}"
    let actual ← Lean.collectAxioms decl
    unless actual.size == expected.size && actual.all (expected.contains ·) do
      throwError "Unexpected axioms for {decl}: {actual}"

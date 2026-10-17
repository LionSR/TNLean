/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.MessageGateSegmentExpansion
import Lean.Util.CollectAxioms

/-! # Logical dependencies of expansion of message-free weighted segments -/

run_cmd do
  let decl := `TNLean.PEPS.PairEffect.MessageGate.expand_map_segment
  unless (← Lean.getEnv).contains decl do
    throwError "The intended segment expansion theorem is absent: {decl}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected logical dependencies for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"

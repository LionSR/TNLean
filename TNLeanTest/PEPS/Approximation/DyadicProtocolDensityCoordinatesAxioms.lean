/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicProtocolDensityCoordinates
import Lean.Util.CollectAxioms

/-! Standard-axiom checks for the actual protocol density in site coordinates. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  let names := #[
    ``TNLean.PEPS.Approximation.DyadicProtocol.reindex_original_physicalDensity,
    ``TNLean.PEPS.Approximation.DyadicProtocol.rectangularTraceNorm_reindex_sub_physicalDensity]
  for decl in names do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

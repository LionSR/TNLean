/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicProtocolPhysicalReadout
import Lean.Util.CollectAxioms

/-! Standard-axiom checks for the protocol's actual folded physical coordinates. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in #[``TNLean.PEPS.Approximation.DyadicProtocol.physicalConfigEquiv_apply_val,
      ``TNLean.PEPS.Approximation.DyadicProtocol.physicalConfigEquiv_symm_apply_site_val,
      ``TNLean.PEPS.Approximation.DyadicProtocol.physicalConfigEquiv_symm_apply_eq_of_not_mem_range,
      ``TNLean.PEPS.Approximation.DyadicProtocol.physicalReadout,
      ``TNLean.PEPS.Approximation.DyadicProtocol.foldVertex_anchor_site,
      ``TNLean.PEPS.Approximation.DyadicProtocol.physicalReadout_fold_eq_symm,
      ``TNLean.PEPS.Approximation.DyadicProtocol.bijective_physicalReadout_fold] do
    unless env.contains decl do
      throwError "Missing imported declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicPatchRewriteGates
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom guard for the small-patch rewrites of the dyadic protocol

The rewrites of the junction resizes and the direct repaintings, the used-party property of their
parties, and the lifetime participation bound for schedules of such rewrites must exist in the
production module and depend only on standard logical axioms.
-/

set_option linter.hashCommand false

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in #[``TNLean.PEPS.Approximation.GuidePatchRewrite.parties_subset,
      ``TNLean.PEPS.Approximation.junctionUses_of_blockGuide_eq,
      ``TNLean.PEPS.Approximation.repaintingUses_of_blockGuide_eq,
      ``TNLean.PEPS.Approximation.GuidePatchRewrite.IsJunctionResize.uses,
      ``TNLean.PEPS.Approximation.GuidePatchRewrite.IsDirectRepainting.uses,
      ``TNLean.PEPS.Approximation.exists_junctionResize,
      ``TNLean.PEPS.Approximation.exists_directRepainting,
      ``TNLean.PEPS.Approximation.card_gates_le_of_guidePatchRewrites] do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

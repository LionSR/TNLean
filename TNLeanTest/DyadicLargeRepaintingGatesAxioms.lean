/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicLargeRepaintingGates
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom guard for the gates of the large-scale repaintings

The locality of the guides of a large-scale repainting, the used-party property of its gates, the
patch nets of its point treatments and bulk steps, and the lifetime participation bound for
schedules with large-scale repaintings must exist in the production module and depend only on
standard logical axioms.
-/

set_option linter.hashCommand false

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in #[``TNLean.PEPS.Approximation.RepaintingBaseline.isLocalGuide_mainGuide,
      ``TNLean.PEPS.Approximation.RepaintingBaseline.isLocalGuide_auxGuide,
      ``TNLean.PEPS.Approximation.RepaintingBaseline.isLocalGuide_treatedStartMain,
      ``TNLean.PEPS.Approximation.RepaintingBaseline.isLocalGuide_treatedAux,
      ``TNLean.PEPS.Approximation.RepaintingBaseline.IsLocalGuide.homogenize,
      ``TNLean.PEPS.Approximation.RepaintingBaseline.IsLocalGuide.piecewise,
      ``TNLean.PEPS.Approximation.RepaintingBaseline.isLocalGuide_exchangedMain,
      ``TNLean.PEPS.Approximation.RepaintingBaseline.isLocalGuide_exchangedAux,
      ``TNLean.PEPS.Approximation.RepaintingBaseline.IsLocalGuide.changed_subset,
      ``TNLean.PEPS.Approximation.repaintingUses_of_mem_localLabels,
      ``TNLean.PEPS.Approximation.GuidePatchRewrite.IsLargeRepaintingStep.uses,
      ``TNLean.PEPS.Approximation.exists_pointTreatment,
      ``TNLean.PEPS.Approximation.exists_bulkStep,
      ``TNLean.PEPS.Approximation.card_gates_le_of_repaintingRewrites] do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
